module Sedris

import public Sedris.Lang
import public Sedris.Pure

export
interpret : (sc : Script sx) -> {auto 0 isPure : PureScript sc} -> String -> List String
interpret [] {isPure = IsNil} str = []
interpret ((_ * _) :: _) _ impossible
interpret (|*> _ :: _) _ impossible
interpret (([] *> _) :: sc) {isPure = IsConsFileScript isPure} str
  = interpret sc str
interpret (((z :: xs) *> x) :: y) {isPure = isPure} str = ?interpret_rhs_7
interpret ((|> x) :: y) {isPure = isPure} str = ?interpret_rhs_5

export
interpretIO : (sc : Script sx) -> String -> IO (Either String (List String))