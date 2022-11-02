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
    , > WithHoldContent "filename" (\f => [ > WriteTo (outFile f)
                                          , > Print])
    ]
  ] where
  outFile : (String, String, String) -> (String, String, String)
  outFile (path, name, ext) = (path, name ++ "_out", ext)

source : IOFile
source = ("", "replaces_in", ".txt")

f1 : IOFile
f1 = ("", "subs1", ".txt")

test : IO ()
test =
  do res <- interpretIO (replacesFromCSV source [f1]) ""
     case res of
      Left p => putStr (show p)
      Right r => putStr (joinBy "\n" (cast r))
      
