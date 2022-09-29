module Sedris.Replace

import Sedris.Lang
import Data.DPair

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

export
performReplace : String -> ReplaceCommand -> String
performReplace str (All pattern substitution)
  = pack $ substituteAll (unpack pattern) (unpack substitution) [<] (unpack str)
performReplace str (AllMulti xs) = ?performReplace_rhs_1
performReplace str (AllMulti' xs ys) = ?performReplace_rhs_2
performReplace str (Prefix str1 str2) = ?performReplace_rhs_3
performReplace str (Suffix str1 str2) = ?performReplace_rhs_4
performReplace str (AllRe x f) = ?performReplace_rhs_5
performReplace str (PrefixRe x f) = ?performReplace_rhs_6
performReplace str (SuffixRe x f) = ?performReplace_rhs_7
performReplace str (CharSubst xs) = ?performReplace_rhs_8
performReplace str (CharSubst' xs ys) = ?performReplace_rhs_9