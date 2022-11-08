import Sedris

simpleReplace : (re : TyRE a) -> {auto 0 consuming : IsConsuming re}
              -> (a -> String) -> IOFile -> Script [<] IO
simpleReplace tyre toStr file =
  [ |> CreateHold "filename" ""
  , [file] *
    [ Line 1 ?> FileName "filename"
    , Line 1 ?> WithHoldContent "filename" (\f => [ > ClearFile (outFile f)])
    , > Replace (AllRe tyre toStr)
    , > WithHoldContent "filename" (\f => [ > WriteTo (outFile f)])]
  ] where
  outFile : String -> String
  outFile str =
    let (_, name, ext) := splitFilePath str
    in name ++ "_out" ++ "." ++ ext

simpleReplaceLocal : (re : TyRE a) -> {auto 0 consuming : IsConsuming re}
                  -> (a -> String) -> (List String) -> Script [<] Local
simpleReplaceLocal tyre toStr lines =
  [ lines *>
    [ > Replace (AllRe tyre toStr)
    , > Print ]
  ]

test1 : IO ()
test1 =
  let script := simpleReplaceLocal (r "al[aei]!") (("ol" ++) . cast)
                  [ "ala ma kota, kot ma ale"
                  , "gdzie jest ala?"
                  , "czy ktos widzial ale?"
                  , "czy ten kot jest ali czy nie?"]
  in putStr $ unlines $ cast $ interpret script ""