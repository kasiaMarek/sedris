import Sedris.Lang

Ex1 : Script [<]
Ex1 = ["filename.txt"] *
      [ > Routine "whatnot"
          [ > Replace (All "foo" "bar")]
      , Line 3 ?> Call "whatnot"
      , > Call "whatnot"
      , > HoldGlobal "number" (\_ => (the Nat 1))
      , > FromHold "number" (\_ => the (Nat -> String) show)
      ]
  ++  [] *
      [ > FromHold "number" (\_ => the (Nat -> String) show)
      ]
  ++  End