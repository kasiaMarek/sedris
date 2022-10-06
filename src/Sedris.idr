module Sedris

import public Sedris.Lang
import Sedris.Interpret
import public Data.Regex

export
interpret : (sc : Script [<] Local) -> String -> SnocList String
interpret sc str = interpretS (Just sc) (init str)

namespace SimpleUse
  export
  interpret : (sc : Script [<] Local) -> String
  interpret sc = unlines $ cast $ interpret sc ""

export
interpretIO : (sc : Script [<] st) -> String -> IO (Either String (List String))