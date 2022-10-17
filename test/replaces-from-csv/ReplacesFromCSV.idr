import Sedris.Lang

import Data.String

replacesFromCSV : IOFile -> List IOFile -> Script [<] IO
replacesFromCSV source files =
  [ |> CreateHold "map" (the (List (String, String)) [])
  , [source] *
    [ > HoldApp "map"
                (\acc,str =>  let (head ::: xs) := split (== ',') str
                              in acc ++ map (\x => (head, x)) xs)]
  , |> CreateHold "filename" ("", "", "")
  , files *
    [ Line 1 ?> FileName "filename"
    , Line 1 ?> WithHoldContent "filename" (\f => [ > ClearFile (outFile f)])
    , > WithHoldContent "map" {t = List (String, String)}
          (foldr  (\el,acc =>
                    (> Replace (All (Builtin.fst el) (Builtin.snd el))) :: acc)
                  [])
    , > WithHoldContent "filename" (\f => [ > WriteTo (outFile f)])
    ]
  ] where
  outFile : (String, String, String) -> (String, String, String)
  outFile (_, name, ext) = ("out", name, ext)

