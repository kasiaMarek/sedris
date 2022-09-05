import Sedris.Lang

wordCount : String -> Script [<]
wordCount fileName
  = [fileName] *
    [ Line 1 ?> Hold "count" (const Z)
    , > HoldApp "count" (\curr,line => curr + wc line)
    , LastLine ?> FromHold "count" (const $ the (Nat -> String) show)
    , LastLine ?> Print]
  ++ End where
    wc : String -> Nat
    wc str = length $
      asDisjointMatches (Untyped $ CharPred $ Pred (/= ' ')) str True
