module Main

import Test.Golden

%default covering

core : TestPool
core = MkTestPool "core" [] Nothing
      [ "simple-replace"
      , "word-count"
      ]

main : IO ()
main = runner [ core ]
