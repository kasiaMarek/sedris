import Sedris

tail : Nat -> IOFile -> Script [<] IO
tail count fileName =
  [ |> CreateHold "lns" {t = List String} []
  , [fileName] *
    [ > HoldApp "lns" (\l,s => l ++ [s])
    , Not (LineRange 1 count) ?> ExecOnHold "lns" {t = List String}
                                         ((fromMaybe []) . tail')]
  , |> FromHold "lns" (const $ joinBy "\n")
  , |> PrintStd
  ]

last3lines : IO ()
last3lines =
  do res <- interpretIO (tail 3 ("", "lastlines", ".txt")) ""
     case res of
      Left p => putStr (show p)
      Right r => putStr ""
