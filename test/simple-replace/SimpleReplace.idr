import Sedris.Lang

simpleReplace : (TyRE a) -> (a -> String) -> String -> Script [<] IO
simpleReplace tyre toStr file =
  [ (file ::: []) *
    [ Line 1 ?> ClearFile outFile
    , > Replace (AllRe tyre toStr)
    , > WriteTo outFile ]
  ] where
  outFile : (String, String, String) -> (String, String, String)
  outFile (path, name, ext) = (path, name ++ "_out", ext)

simpleReplaceLocal : (TyRE a) -> (a -> String) -> (List String) -> Script [<] Local
simpleReplaceLocal tyre toStr lines =
  [ lines *>
    [ > Replace (AllRe tyre toStr)
    , > Print ]
  ]