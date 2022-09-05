import Sedris.Lang

replacesFromCSV : String -> List String -> Script [<]
replacesFromCSV source files =
  [source] *
  [Line 1 ?> HoldGlobal "map" {t = List (String, String)} (const [])]
  ++ files *
  [ > WithHoldContent "map"
                      (\replaces => [ > Replace (AllMulti replaces)])
  , > Print
  ]
  ++ End
