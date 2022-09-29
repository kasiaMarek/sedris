module Sedris

import public Sedris.Lang
import public Sedris.Replace
import public Sedris.Extra
import public Sedris.VariableStore

import Data.DPair

0 getAllVarsFileScript : FileScript sx t -> List (VarType, String)
getAllVarsFileScript [] = []
getAllVarsFileScript ((::) cmd {ys} fsc) = ys ++ getAllVarsFileScript fsc

0 getAllVars : Script sx t -> List (VarType, String)
getAllVars [] = []
getAllVars ((::) cmd {ys} sc) = ys ++ getAllVars sc

record VMState (sx : Variables) (st : FileScriptType) where
  constructor MkVMState
  patternSpace : String
  resultSpace : SnocList String
  variables : LinkedListStore sx st

init : String -> VMState [<] st
init str = MkVMState str [<] empty

lift : (LinkedListStore sx st -> LinkedListStore sx' st')
    -> (VMState sx st -> VMState sx' st')
lift f (MkVMState patternSpace resultSpace variables)
  = MkVMState { patternSpace
              , resultSpace
              , variables = f variables }

mutual
  interpretCommand : (cmd : Command sx ys Local) -> VMState sx Local
                  -> Either (SnocList String)
                            (VMState (sx <>< ys) Local) -- left if we quit mid-exec
  interpretCommand  (Replace replace)
                    (MkVMState patternSpace resultSpace variables)
    = Right $ MkVMState { patternSpace = performReplace patternSpace replace
                        , resultSpace
                        , variables }
  interpretCommand  (Exec f)
                    (MkVMState patternSpace resultSpace variables)
    = Right $ MkVMState { patternSpace = f patternSpace
                        , resultSpace
                        , variables }
  interpretCommand  Print
                    (MkVMState patternSpace resultSpace variables)
    = Right $ MkVMState { patternSpace = ""
                        , resultSpace = resultSpace :< patternSpace
                        , variables }
  interpretCommand  (CreateHold hs {t} initVal)
                    (MkVMState patternSpace resultSpace variables)
    = Right $ MkVMState { patternSpace
                        , resultSpace
                        , variables = holdSpace hs initVal variables }
  interpretCommand  (HoldApp holdSpace f {pos})
                    (MkVMState patternSpace resultSpace variables)
    = Right $ MkVMState { patternSpace
                    , resultSpace
                    , variables =
                        execOnHoldSpace pos variables (\v => f v patternSpace) }
  interpretCommand  (FromHold holdSpace f {pos})
                    (MkVMState patternSpace resultSpace variables)
    = Right $ MkVMState { patternSpace
                            = f patternSpace (getHoldSpace pos variables)
                        , resultSpace
                        , variables }
  interpretCommand  (ExecOnHold holdSpace f {pos})
                    (MkVMState patternSpace resultSpace variables)
    = Right $ MkVMState { patternSpace
                        , resultSpace
                        , variables = execOnHoldSpace pos variables f }
  interpretCommand  (Call label {pos})
                    (MkVMState patternSpace resultSpace variables)
    = ?H1
      {-
      let Evidence sx' (sc, hs, f) := getRoutine pos variables
      in map  (lift $ f . (\x => trim x (length hs) {ford = lengthPrf hs}))
              (interpretAux sc (MkVMState patternSpace resultSpace hs))
      -}
  interpretCommand  (WithHoldContent holdSpace f {pos})
                    (MkVMState patternSpace resultSpace variables)
    = let (hs', hsF) := withOut variables pos
      in map  (lift $ hsF . (\x => trim x (length hs') {ford = lengthPrf hs'}))
              (interpretAux   (f $ getHoldSpace pos variables)
                              (MkVMState patternSpace resultSpace hs'))
  interpretCommand  Quit
                    (MkVMState patternSpace resultSpace variables)
    = Left $ resultSpace
  interpretCommand  (Routine name sc)
                    (MkVMState patternSpace resultSpace variables)
    = Right $ MkVMState { patternSpace
                        , resultSpace
                        , variables = label name sc variables
                        }
  interpretCommand  (IfThenElse f sc1 sc2)
                    state@(MkVMState patternSpace resultSpace variables)
    = if (f patternSpace)
      then map  (lift (\x => trim x (length variables)
                                  {ford = lengthPrf variables}))
                (interpretAux sc1 state)
      else map  (lift (\x => trim x (length variables)
                                  {ford = lengthPrf variables}))
                (interpretAux sc2 state)

  interpretFileCommand : (cmd : LineCommand sx ys Local) -> VMState sx Local
                      -> Either (SnocList String)
                                (VMState (sx <>< ys) Local)
  interpretFileCommand  Zap (MkVMState patternSpace resultSpace variables)
    = Right $ MkVMState { patternSpace = ""
                        , resultSpace
                        , variables }
  interpretFileCommand  ZapFstLine
                        (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_2
  interpretFileCommand  ReadApp (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_3
  interpretFileCommand Put (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_4
  interpretFileCommand LineNumber (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_5
  interpretFileCommand NewCycle (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_6
  interpretFileCommand  (ReadFrom x)
                        (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_7
  interpretFileCommand  (QueueRead x)
                        (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_8
  interpretFileCommand  (LineRoutine label x)
                        (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_9
  interpretFileCommand  (LineIfThenElse f x y)
                        (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_10
  interpretFileCommand  (CallLineRoutine label {pos})
                        (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_19
  interpretFileCommand  (LineWithHoldContent holdSpace f)
                        (MkVMState patternSpace resultSpace variables)
    = ?interpretFileCommand_rhs_11
  interpretFileCommand (PrintStd {isIO}) vm impossible
  interpretFileCommand (WriteTo f {isIO}) vm impossible
  interpretFileCommand (WriteLineTo f {isIO}) vm impossible
  interpretFileCommand (ClearFile f {isIO}) vm impossible
  interpretFileCommand (FileName {isIO}) vm impossible

  interpretFileScriptForLine
    : (fsc : FileScript sx Local)
    -> VMState sx Local
    -> String
    -> Either (SnocList String)
              (VMState (sx <>< getAllVarsFileScript fsc) Local)
  interpretFileScriptForLine [] vm str = Right vm
  interpretFileScriptForLine ((Sedris.Lang.(>) cmd) :: fsc) vm str
    = ?interpretFileScriptForLine_rhs_2
  interpretFileScriptForLine ((Sedris.Lang.(?>) addr cmd) :: fsc) vm str
    = ?interpretFileScriptForLine_rhs_3
  interpretFileScriptForLine ((addr ?: fsc') :: fsc) vm str
    = ?interpretFileScriptForLine_rhs_4

  interpretFileScript : (fsc : FileScript sx Local)
                      -> List String
                      -> VMState sx Local
                      -> Either (SnocList String) (VMState sx Local)
  interpretFileScript fsc [] vm = Right vm
  interpretFileScript fsc (l :: tail) vm
    = interpretFileScriptForLine fsc vm l
        >>= ( interpretFileScript fsc tail
            . (lift $ (\x => trim x (length vm.variables)
                                  {ford = lengthPrf vm.variables})))

  export
  interpretAux : (sc : Script sx Local)
              -> VMState sx Local
              -> Either (SnocList String)
                        (VMState (sx <>< getAllVars sc) Local)
  interpretAux [] vm = Right vm
  interpretAux ((strs *> fsc) :: sc) vm
    = interpretFileScript fsc strs vm >>= interpretAux sc
  interpretAux ((::) (|> cmd) sc {ys}) vmSt
    = interpretCommand cmd vmSt
      >>= (\vm => map (\res =>
                        replace {p = (\x => VMState x Local)} fishConcat res)
                      (interpretAux sc vm))

export
interpret : (sc : Script [<] Local) -> String -> SnocList String
interpret sc str = ?nceiown
  -- let Evidence (MkVMState _ resultSpace _) := interpretAux sc (init str)
  -- in resultSpace

export
interpretIO : (sc : Script [<] st) -> String -> IO (Either String (List String))
