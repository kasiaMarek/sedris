module Sedris.Replace

import Sedris.Lang
import Data.DPair
import Data.Regex

import Decidable.Equality

doesPrefixMatch : (pattern : List Char) -> (word : List Char)
                -> Maybe (List Char) --possibly return tail
doesPrefixMatch [] word = Just word
doesPrefixMatch (x :: xs) [] = Nothing
doesPrefixMatch (x :: xs) (y :: ys) with (decEq x y)
  doesPrefixMatch (c :: xs) (c :: ys) | (Yes Refl) = doesPrefixMatch xs ys
  doesPrefixMatch (x :: xs) (y :: ys) | (No _) = Nothing

substituteAll : (pattern : List Char)
              -> (replace : List Char)
              -> (proccessed : SnocList Char)
              -> (word : List Char)
              -> List Char
substituteAll pattern replace proccessed [] = cast proccessed
substituteAll pattern replace proccessed (c :: cs) =
  case doesPrefixMatch pattern (c :: cs) of
    Nothing => substituteAll pattern replace (proccessed :< c) cs
    Just tail => substituteAll pattern replace (proccessed <>< replace) tail

replacePrefix : (word : List Char)
              -> (pattern : List Char)
              -> (replace : List Char)
              -> List Char
replacePrefix word pattern replace
  = case doesPrefixMatch pattern word of
      Nothing   => word
      Just tail => word ++ tail

export
performReplace : String -> ReplaceCommand -> String
performReplace str (All pattern substitution)
  = pack $ substituteAll (unpack pattern) (unpack substitution) [<] (unpack str)
performReplace str (Prefix pattern replace)
  = pack $ replacePrefix (unpack str) (unpack pattern) (unpack replace)
performReplace str (Suffix pattern replace) = pack $ reverse
  $ replacePrefix (reverse $ unpack str) (reverse $ unpack pattern)
                        (reverse $ unpack replace)
performReplace str (AllRe re f)
  = toString f (asDisjointMatches re str True)
performReplace str (PrefixRe re f) =
  case parsePrefix re str of
    Nothing => str
    (Just (tree, tail)) => f tree ++ tail
performReplace str (CharSubst xs) = pack $ cast
  $ foldl (\acc,c => acc :< fromMaybe c (map snd (find (\c' => fst c' == c) xs)))
          (the (SnocList Char) $ [<])
          (unpack str)