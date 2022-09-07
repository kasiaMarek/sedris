import Sedris.Lang

import Data.String

replacesFromCSV : String -> List String -> Script [<]
replacesFromCSV source files =
  [ |> CreateHold "map" (the (List (String, String)) [])
  , [source] *
    [ > HoldApp "map"
                (\acc,str =>  let (head ::: xs) := split (== ',') str
                              in acc ++ map (\x => (head, x)) xs)]
  , files *
    [ Line 1 ?> ClearFileDep outFile
    , > WithHoldContent "map"
                        (\replaces => [ |> Replace (AllMulti replaces)])
    , > WriteToDep outFile
    ]
  ] where
  outFile : (String, String, String) -> String
  outFile (_, name, ext) = "out/" ++ name ++ "." ++ ext

