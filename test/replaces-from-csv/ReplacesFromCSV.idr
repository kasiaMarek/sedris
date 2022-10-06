import Sedris.Lang

import Data.String

replacesFromCSV : String -> List1 String -> Script [<] IO
replacesFromCSV source files =
  [ |> CreateHold "map" (the (List (String, String)) [])
  , (source ::: []) *
    [ > HoldApp "map"
                (\acc,str =>  let (head ::: xs) := split (== ',') str
                              in acc ++ map (\x => (head, x)) xs)]
  , files *
    [ Line 1 ?> ClearFile outFile
    , > WithHoldContent "map" {t = List (String, String)}
          (foldr  (\el,acc =>
                    (> Replace (All (Builtin.fst el) (Builtin.snd el))) :: acc)
                  [])
    , > WriteTo outFile
    ]
  ] where
  outFile : (String, String, String) -> (String, String, String)
  outFile (_, name, ext) = ("out", name, ext)

