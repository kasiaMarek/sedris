import Sedris

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
          (foldr (\case (sub, text) => (> Replace (All text sub) ::)) [])
    , > WithHoldContent "filename" (\f => [ > WriteTo (outFile f)])
    ]
  ] where
  outFile : (String, String, String) -> (String, String, String)
  outFile (path, name, ext) = (path, name ++ "_out", ext)

source : IOFile
source = ("replaces-from-csv/", "replaces_in", ".txt")

f1 : IOFile
f1 = ("replaces-from-csv/", "subs1", ".txt")

test : IO ()
test =
  map (\_ => ())
      (interpretIO (replacesFromCSV source [f1]) "")
