module Pretty (
    Pretty (..),
    pretty,
    PrettyM,
    ShortText,
    Doc,
    sexpr,
    fresh,
    PP.text,
    PP.integer,
    ) where

import Control.Monad.Trans.State.Strict
import Data.Char                        (isDigit)
import Data.Text.Short                  (ShortText)
import Data.Void                        (Void, absurd)

import qualified Data.Text.Short  as TS
import qualified Text.PrettyPrint as PP

import qualified Data.Set as Set

type S = Set.Set ShortText
type Doc = PP.Doc
type PrettyM = State S

pretty :: Pretty a => a -> String
pretty x = PP.render (evalState (ppr x) Set.empty)

markUsed :: ShortText -> State S ()
markUsed t = modify' (Set.insert t)

sexpr :: Doc -> [Doc] -> Doc
sexpr car cdr = PP.parens $ PP.hang car 2 $ PP.sep cdr

fresh :: String -> PrettyM String
fresh s = state (pick names)
  where
    pick []       u = (s, u) -- shouldn't happen, names is infinite
    pick (x : xs) u
        | x' `Set.member` u = pick xs u
        | otherwise         = (x, Set.insert x' u)
      where
        x' = TS.pack x

    names = n : [ n ++ show m | m <- [d .. ] ]

    (ds, rn) = span isDigit (reverse s)

    n :: String
    n = reverse rn

    d :: Int
    d = case ds of
      [] -> 0
      _  -> read (reverse ds)

class Pretty a where
    ppr :: a -> PrettyM Doc

instance Pretty ShortText where
    ppr t = do
        markUsed t
        return $ PP.text $ TS.unpack t

instance Pretty Void where
    ppr = absurd
