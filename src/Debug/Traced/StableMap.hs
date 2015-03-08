module Debug.Traced.StableMap(StableMap, empty, insert, Debug.Traced.StableMap.lookup) where
import qualified Data.IntMap as M
import System.Mem.StableName

newtype StableMap a b = S (M.IntMap [(StableName a, b)])

empty :: StableMap a b
empty = S M.empty

insert :: StableName a -> b -> StableMap a b -> StableMap a b
insert k v (S m) = S (M.insertWith (++) (hashStableName k) [(k, v)] m)

lookup :: StableName a -> StableMap a b -> Maybe b
lookup k (S m) = do
    xs <- M.lookup (hashStableName k) m
    Prelude.lookup k xs
