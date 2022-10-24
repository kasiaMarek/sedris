import Sedris

wordCount : IOFile -> Script [<] IO
wordCount fileName
  = [ |> CreateHold "count" Z
    , [fileName] *
      [ > HoldApp "count" (\curr,line => curr + wc line)
      , LastLine ?> FromHold "count" (const $ the (Nat -> String) show)
      , LastLine ?> Print]
  ] where
    wc : String -> Nat
    wc str = length
      $ asDisjointMatches (rep1 $ Untyped $ CharPred $ Pred (/= ' ')) str True

wordCountLocal : List String -> Script [<] Local
wordCountLocal lines
  = [ |> CreateHold "count" Z
    , lines *>
      [ > HoldApp "count" (\curr,line => curr + wc line)
      , LastLine ?> FromHold "count" (const $ the (Nat -> String) show)
      , LastLine ?> Print]
  ] where
    wc : String -> Nat
    wc str = length
      $ asDisjointMatches (rep1 $ Untyped $ CharPred $ Pred (/= ' ')) str True

text : String
text =
"""
Lorem ipsum dolor sit amet. Qui itaque voluptas et facilis velit qui voluptas maiores. Aut error cupiditate non eligendi nisi non sunt quaerat rem galisum soluta est voluptas rerum et enim quaerat ab atque officiis. Est nobis nesciunt qui architecto quaerat et Quis autem 33 numquam earum et voluptas ipsam et saepe illum. Et illo rerum aut corrupti incidunt in dolorem sunt.

Ut error tempore eos alias odit sed esse iste hic quos culpa. Et mollitia similique sit doloribus numquam ab quia omnis. Id facere quidem aut officiis consequatur et illum excepturi a dicta quisquam aut iure suscipit 33 magnam explicabo? Quo rerum voluptas sit nisi dolorum quo nesciunt accusantium et soluta repudiandae cum repellendus reiciendis et rerum rerum qui officiis sequi.

Nam quisquam iste et maiores ducimus et iure perferendis quo voluptatem consequuntur est ipsum quia. Ea maxime incidunt qui nobis dicta ut perferendis asperiores et omnis laborum. Sed praesentium rerum At libero maiores non impedit vitae ea officiis placeat. Non voluptatem libero ut quas quaerat qui tempore ipsam aut dicta culpa quo atque assumenda ut quae quis.
"""

test1 : IO ()
test1 = putStr $ unlines $ cast $ interpret (wordCountLocal (lines text)) ""