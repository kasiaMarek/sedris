import Sedris.Lang

Ex1 : Script [<] IO
Ex1 =
  [ ("filename.txt" ::: []) *
    [ > Routine "whatnot"
        [ > Replace (All "foo" "bar")]
    , Line 3 ?> Call "whatnot"
    , > Call "whatnot"
    ]
  , |> CreateHold "number" (the Nat 1)
  , |*>
    [ > FromHold "number" (\_ => the (Nat -> String) show)
    ]
  ]