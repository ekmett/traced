{-# LANGUAGE CPP, ExistentialQuantification, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances, FlexibleContexts, DeriveDataTypeable #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE OverlappingInstances #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2012-15 Edward Kmett, 2008-2009 Lennart Augustsson
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module Debug.Traced.Internal
  ( Traced, traced
  , named, nameTraced
  , unknown, unTraced
  , tracedD
  , TraceLevel(..), Traceable(..)
  , TracedD(..), unTracedD
  , binOp, unOp, apply
  , liftT, liftFun, Liftable(..), baseLiftT
  , Fixity(..)
  , showAsExp, showAsExpFull
  , pPrintTraced
  , reShare, simplify
  ) where

import System.Mem.StableName
import System.IO.Unsafe(unsafePerformIO)
import Data.Typeable
#if __GLASGOW_HASKELL__ >= 704
import Data.Data(Data(..), mkNoRepType)
#elif __GLASGOW_HASKELL__ >= 610
import Data.Data(Data(..), mkNorepType)
#else
import Data.Generics(Data(..), mkNorepType)
#endif
import Control.Monad.State
import Data.Maybe(fromMaybe)
import Data.List(group, sort)
import Data.Char(isAlpha)
import qualified Data.Map as M
import qualified Data.Set as S
import Text.PrettyPrint.HughesPJ
--import Debug.Trace

import qualified Debug.Traced.StableMap as SM

-- | Traced values of some type.
data Traced a = Traced (Maybe TracedD) a
  deriving (Typeable, Data)

instance (Read a, Traceable a) => Read (Traced a) where
  readsPrec p s = [ (traced x, r) | (x, r) <- readsPrec p s]

data TraceLevel = TLValue | TLExp | TLFullExp
  deriving (Eq, Ord, Show, Typeable, Data)

class (Typeable a, Show a) => Traceable a where
  trPPrint :: TraceLevel -> Int -> a -> Doc

instance (Typeable a, Show a) => Traceable a where
  trPPrint _ p x = text (showsPrec p x "")

-- | Expression tree for a traced value.
data TracedD
  = NoValue                                                    -- ^unknown value
  | forall a . Name Bool Name TracedD                          -- ^value with a name
  | forall a . (Traceable a) => Con a                          -- ^constant
  | forall a . (Traceable a) => Apply a Name Fixity [TracedD]  -- ^application
  | forall a . Let [(Name, TracedD)] TracedD                   -- ^(recovered) let expression
  deriving (Typeable)

type Name = String

instance Data TracedD where
  gfoldl _ z c = z c
  gunfold _ _ _ = error "gunfold: TracedD"
  toConstr _ = error "toConstr: TracedD"
#if __GLASGOW_HASKELL__ >= 704
  dataTypeOf _ = mkNoRepType "Debug.TracedInternal.TracedD"
#else
  dataTypeOf _ = mkNorepType "Debug.TracedInternal.TracedD"
#endif

instance Show TracedD where
  showsPrec _ NoValue = showString "__NoValue__"
  showsPrec p (Name _ _ v) = showsPrec p v
  showsPrec p (Con a) = showsPrec p a
  showsPrec p (Apply a _ _ _) = showsPrec p a
  showsPrec p (Let _ v) = showsPrec p v

instance Eq TracedD where
  x == y  =  compare x y == EQ

-- Pure structural comparison, good for putting values into a map
instance Ord TracedD where
  compare NoValue             NoValue             = EQ
  compare NoValue             _                   = LT
  compare Name{}              NoValue             = GT
  compare (Name b1 n1 v1)     (Name b2 n2 v2)     = compare (b1, n1, v1) (b2, n2, v2)
  compare Name{}              _                   = LT
  compare Con{}               NoValue             = GT
  compare Con{}               Name{}              = GT
  compare (Con a1)            (Con a2)            = compareValues a1 a2
  compare Con{}               _                   = LT
  compare (Apply _ n1 f1 as1) (Apply _ n2 f2 as2) = compare (n1, f1, as1) (n2, f2, as2)
  compare Apply{}             Let{}               = LT
  compare Apply{}             _                   = GT
  compare (Let bs1 t1)        (Let bs2 t2)        = compare (bs1, t1) (bs2, t2)
  compare Let{}               _                   = GT

-- We need an ordering on values (possibly of different types).
-- It doesn't matter what the ordering is, as long as it's total.
-- We fudge it by using the hash of the stable name as the unique
-- identifier for the value and the compare those.
compareValues :: (Traceable a, Traceable b) => a -> b -> Ordering
compareValues x y = compare (uniq x) (uniq y) where
  uniq a = seq a $ hashStableName (unsafePerformIO $ makeStableName a)

-- |Fixity for identifier.
data Fixity = InfixL Int | InfixR Int | Infix Int | Nonfix
  deriving (Eq, Ord, Show)

eLet :: [(Name, TracedD)] -> TracedD -> TracedD
eLet [] e = e
eLet bs e = Let bs e

-- | Create a traced value.
traced :: (Traceable a) => a -> Traced a
traced a = Traced Nothing a

-- | Add a named to a traced value.
nameTraced :: (Traceable a) => String -> Traced a -> Traced a
nameTraced s t@(Traced (Just (Name False s' _)) _) | s == s' = t
nameTraced s t@(Traced _ a) = Traced (Just $ Name False s $ tracedD t) a

-- | Create a named traced value.
named :: (Traceable a) => String -> a -> Traced a
named s a = nameTraced s $ traced a

-- | Create a named thing with no value.  Cannot be used where a real value is needed.
unknown :: (Traceable a) => String -> Traced a
unknown s = Traced (Just (Name False s NoValue)) (error $ "Data.Traced: unknown `" ++ s ++ "' used")

-- | Extract the real value from a traced value.
unTraced :: Traced a -> a
unTraced (Traced _ a) = a

-- | Extract the expression tree from a traced value.
tracedD :: (Traceable a) => Traced a -> TracedD
tracedD (Traced (Just d) _) = d
tracedD (Traced Nothing a) = Con a

-- | Convert an expression tree to a traced value, if the types are correct.
unTracedD :: (Traceable a) => TracedD -> Maybe (Traced a)
unTracedD e = case e of
  NoValue -> Just $ trcd (error "unTraced: no value")
  Name _ n NoValue -> Just $ trcd (error $ "unTraced: no value: " ++ n)
  Name _ _ v -> liftM (trcd . unTraced) $ unTracedD v
  Con a -> liftM trcd $ cast a
  Apply a _ _ _ -> liftM trcd $ cast a
  Let _ v -> liftM (trcd . unTraced) $ unTracedD v
  where trcd = Traced (Just e)

-- |Create a traced value with an 'Apply' expression tree.
apply :: (Traceable a) => a -> Name -> Fixity -> [TracedD] -> Traced a
apply r op fx as = Traced (Just $ Apply r op fx as) r

class Liftable a b | a -> b, b -> a where
  liftT' :: Name -> Fixity -> [TracedD] -> a -> b

instance (Traceable a, Liftable b tb) => Liftable (a -> b) (Traced a -> tb) where
  liftT' n fx as f x = liftT' n fx (tracedD x:as) (f (unTraced x))

baseLiftT :: (Traceable a) => Name -> Fixity -> [TracedD] -> a -> Traced a
baseLiftT n fx as r = Traced (Just $ Apply r n fx (reverse as)) r

instance Liftable Integer  (Traced Integer)  where liftT' = baseLiftT
instance Liftable Int      (Traced Int)      where liftT' = baseLiftT
instance Liftable Double   (Traced Double)   where liftT' = baseLiftT
instance Liftable Float    (Traced Float)    where liftT' = baseLiftT
instance Liftable Bool     (Traced Bool)     where liftT' = baseLiftT
instance Liftable Ordering (Traced Ordering) where liftT' = baseLiftT
instance Liftable ()       (Traced ())       where liftT' = baseLiftT

liftT :: (Liftable a b) => Name -> Fixity -> a -> b
liftT n fx = liftT' n fx []

liftFun :: (Liftable a b) => Name -> a -> b
liftFun n = liftT n Nonfix

-----------------------------------

-- Numeric instances

binOp :: (Traceable a, Traceable b, Traceable c) =>
         (a->b->c) -> (String, Fixity) -> Traced a -> Traced b -> Traced c
binOp f (n, fx) x y = apply (unTraced x `f` unTraced y) n fx [tracedD x, tracedD y]

unOp :: (Traceable a, Traceable b) => (a->b) -> String -> Traced a -> Traced b
unOp f op x = apply (f $ unTraced x) op Nonfix [tracedD x]

instance (Eq a) => Eq (Traced a) where
  x == x'  =  unTraced x == unTraced x'

instance (Ord a) => Ord (Traced a) where
  x `compare` x' =  unTraced x `compare` unTraced x'

instance (Show a) => Show (Traced a) where
  showsPrec _ (Traced (Just (Name _ s NoValue)) _) = showString s
  showsPrec p v = showsPrec p $ unTraced v

instance (Traceable a, Num a) => Num (Traced a) where
  (+)           = binOp (+) ("+", InfixL 6)
  (-)           = binOp (-) ("-", InfixL 6)
  (*)           = binOp (*) ("*", InfixL 7)
  negate        = unOp negate "negate"
  abs           = unOp abs    "abs"
  signum        = unOp signum "signum"
  fromInteger   = traced . fromInteger

instance (Traceable a, Fractional a) => Fractional (Traced a) where
  (/)           = binOp (/) ("/", InfixL 7)
  fromRational  = traced . fromRational

instance (Traceable a, Integral a) => Integral (Traced a) where
  quot          = binOp quot ("quot", InfixL 7)
  rem           = binOp rem ("rem", InfixL 7)
  div           = binOp div ("div", InfixL 7)
  mod           = binOp mod ("mod", InfixL 7)
  toInteger     = toInteger . unTraced
  quotRem x y   = (quot x y, rem x y)

instance (Traceable a, Enum a) => Enum (Traced a) where
  toEnum        = traced . toEnum
  fromEnum      = fromEnum . unTraced

instance (Traceable a, Real a) => Real (Traced a) where
  toRational    = toRational . unTraced

instance (Traceable a, RealFrac a) => RealFrac (Traced a) where
  properFraction c = (i, traced c') where (i, c') = properFraction (unTraced c)

instance (Traceable a, Floating a) => Floating (Traced a) where
  pi = named "pi" pi
  exp = unOp exp "exp"
  sqrt = unOp sqrt "sqrt"
  log = unOp log "log"
  (**) = binOp (**) ("**", InfixR 8)
  logBase = binOp logBase ("logBase", Nonfix)
  sin = unOp sin "sin"
  tan = unOp tan "tan"
  cos = unOp cos "cos"
  asin = unOp asin "asin"
  atan = unOp atan "atan"
  acos = unOp acos "acos"
  sinh = unOp sinh "sinh"
  tanh = unOp tanh "tanh"
  cosh = unOp cosh "cosh"
  asinh = unOp asinh "asinh"
  atanh = unOp atanh "atanh"
  acosh = unOp acosh "acosh"

instance (Traceable a, RealFloat a) => RealFloat (Traced a) where
  floatRadix = floatRadix . unTraced
  floatDigits = floatDigits . unTraced
  floatRange  = floatRange . unTraced
  decodeFloat = decodeFloat . unTraced
  encodeFloat m e = traced (encodeFloat m e)
  exponent = exponent . unTraced
  significand = traced . significand . unTraced
  scaleFloat k = traced . scaleFloat k . unTraced
  isNaN = isNaN . unTraced
  isInfinite = isInfinite . unTraced
  isDenormalized = isDenormalized . unTraced
  isNegativeZero = isNegativeZero . unTraced
  isIEEE = isIEEE . unTraced
  atan2 = binOp atan2 ("atan2", Nonfix)


-----------------------------------

-- Pretty printing of a traced value

ppTracedD :: TraceLevel -> Int -> TracedD -> Doc
ppTracedD _     _ NoValue = text "undefined"
ppTracedD _     _ (Name _ n NoValue) = text n

ppTracedD TLValue p (Name _ _ x) = ppTracedD TLValue p x
ppTracedD TLValue p (Con x) = trPPrint TLValue p x
ppTracedD TLValue p (Apply x _ _ _) = trPPrint TLValue p x
ppTracedD TLValue p (Let _ x) = ppTracedD TLValue p x

ppTracedD TLExp p (Name False _ v) = ppTracedD TLExp p v
ppTracedD TLExp _ (Name True s _) = text s
ppTracedD TLFullExp  _ (Name _ n v) = text n <> text "{-" <> trPPrint TLValue 0 v <> text "-}"

ppTracedD b     p (Con v) = trPPrint b p v
ppTracedD _     _ (Apply _ f _ []) = text f
ppTracedD b     p (Apply _ "negate" _ [x]) = -- A hack for negate
    ppParens (p >= 6) (text "-" <> ppTracedD b 7 x)
ppTracedD b     p (Apply _ op Nonfix as) =
    ppParens (p > 10) $
    text op <+> fsep (map (ppTracedD b 11) as)
ppTracedD b     p (Apply _ op f [x,y]) =
    let (ql,q,qr) = case f of
                    InfixL d -> (d,d,d+1)
                    InfixR d -> (d+1,d,d)
                    Infix  d -> (d+1,d,d+1)
                    Nonfix   -> error "ppTracedD: impossible"
        op' = if isAlpha (head op) then "`" ++ op ++ "`" else op
    in  ppParens (p > q) $
        sep [ppTracedD b ql x <+> text op', ppTracedD b qr y]
ppTracedD _     _ Apply{} = error "ppTracedD: bad binop"
ppTracedD b     p (Let bs v) =
    ppParens (p > 0) $
    sep (text "let" : map (nest 4 . ppBind) bs ++ [text "in  " <> ppTracedD b 0 v])
  where ppBind (n, e) = text n <+> equals <+> ppTracedD b 0 e <>
                        if b == TLFullExp then text " {- " <> equals <+> text (show e) <> text " -}" <> semi else semi

ppParens :: Bool -> Doc -> Doc
ppParens False d = d
ppParens True d = parens d

-- |Show the expression tree of a traced value.
showAsExp :: (Traceable a) => Traced a -> String
showAsExp = render . pPrintTraced TLExp 0

-- |Show the expression tree of a traced value, also show the value of each variable.
showAsExpFull :: (Traceable a) => Traced a -> String
showAsExpFull = render . pPrintTraced TLFullExp 0

pPrintTraced :: (Traceable a) => TraceLevel -> Int -> Traced a -> Doc
pPrintTraced b p = ppTracedD b p . tracedD

-----------------------------------

reShare :: (Traceable a) => Traced a -> Traced a
reShare = fromMaybe (error "impossible reShare") . unTracedD . share . tracedD

-- This unsafePerformIO is safe in the sense that it doesn't cause any runtime errors,
-- but it does allow observation of how expressions are evaluated.  That's the whole
-- purpose of it.
share :: TracedD -> TracedD
share e = unsafePerformIO $ do
  (v, (_, _, bs)) <- runStateT (share' e) (0, SM.empty, [])
  let unknownBind (n, Name False n' NoValue) = n == n'
      unknownBind _ = False
  return $ Let (filter (not . unknownBind) $ reverse bs) v

share' :: TracedD -> StateT (Integer, SM.StableMap TracedD TracedD, [(Name, TracedD)]) IO TracedD
share' e@NoValue = return e  -- Don't share constants
share' e@(Con _) = return e  -- Don't share constants
share' e = do
  (i, sm, bs) <- get
  sn <- liftIO $ e `seq` makeStableName e
  case SM.lookup sn sm of
    Just ie -> return ie
    Nothing -> do
      let n = case e of
            Name _ s _ -> s   -- reuse the user name
            _ -> prefix ++ show i
          ie = Name True n e
      put (i+1, SM.insert sn ie sm, bs)
      e' <- case e of
        NoValue -> return e
        Name b m a -> liftM (Name b m) $ share' a
        Con _ -> return e
        Apply a m fx as -> liftM (Apply a m fx) $ mapM share' as
        Let _ _ -> error "share': Let"
      (i', sm', bs') <- get
      put (i', sm', (n, e') : bs')
      return ie

prefix :: String
prefix = "_"

-- |Simplify an expression tree.
simplify :: Traced a -> Traced a
simplify (Traced d a) = Traced (fmap simplifyD d) a

-- Simplify bindings
-- Inline definitions used once and trivial (constants and variables) expressions.
simplifyD :: TracedD -> TracedD
simplifyD elet@(Let binds body) =
  let onceVars = S.fromList $ map head $ filter ((== 1) . length) $ group $ sort $ getVars elet
      getVars NoValue = []
      getVars (Con _) = []
      getVars (Let bs e) = concatMap (getVars . snd) bs ++ getVars e
      getVars (Apply _ _ _ es) = concatMap getVars es
      getVars (Name True v _) = [v]
      getVars (Name False _ e) = getVars e
      isTriv NoValue = True
      isTriv (Con _) = True
      isTriv (Name True _ _) = True
      isTriv _ = False
      subst _ NoValue = NoValue
      subst _ e@(Con _) = e
      subst _ (Let _ _) = error "Traced.simplify: Let"
      subst m (Apply a op fx es) = Apply a op fx (map (subst m) es)
      subst m (Name b v e) = case M.lookup v m of
        Nothing -> Name b v (subst m e)
        Just e' -> e'
      shareVar v = take (length prefix) v == prefix
      (bs', bm) = foldr step ([], M.empty) (reverse binds)
      step (v, e) (ds, m) =
        let e' = subst m e
        in  if shareVar v && (v `S.member` onceVars || isTriv e')
            then (ds, M.insert v e' m)
            else ((v, e') : ds, m)
      body' = subst bm body
  in  eLet (reverse bs') body'
simplifyD e = e

