module Sedris.Pure

import Sedris.Lang

public export
data PureScript : Script sx -> Type where
  IsNil : PureScript []
  IsConsFileScript : PureScript tail
                  -> PureScript ((localFiles *> scr) :: tail)
  IsConsCmd :  PureScript tail
            -> PureScript ((|> cmd) :: tail)