import Sedris

simpleReplace : (re : TyRE a) -> {auto 0 consuming : IsConsuming re}
              -> (a -> String) -> String -> Script [<] IO
simpleReplace tyre toStr file =
  [ (file ::: []) *
    [ Line 1 ?> ClearFile outFile
    , > Replace (AllRe tyre toStr)
    , > WriteTo outFile ]
  ] where
  outFile : (String, String, String) -> (String, String, String)
  outFile (path, name, ext) = (path, name ++ "_out", ext)

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