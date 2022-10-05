import Sedris.Lang

wordCount : String -> Script [<] IO
wordCount fileName
  = [ |> CreateHold "count" Z
    , (fileName ::: []) *
      [ > HoldApp "count" (\curr,line => curr + wc line)
      , LastLine ?> FromHold "count" (const $ the (Nat -> String) show)
      , LastLine ?> Print]
  ] where
    wc : String -> Nat
    wc str = length $
      asDisjointMatches (Untyped $ CharPred $ Pred (/= ' ')) str True
