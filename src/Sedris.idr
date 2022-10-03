module Sedris

import public Sedris.Lang
import public Sedris.Replace
import public Sedris.Extra
import public Sedris.VariableStore

import Data.DPair

-- %default total

getAllVarsCommand : Command sx ys st io -> (vars : List Variable ** vars = ys)
getAllVarsCommand (Replace x) = ([] ** Refl)
getAllVarsCommand (Exec f) = ([] ** Refl)
getAllVarsCommand Print = ([] ** Refl)
getAllVarsCommand (CreateHold holdSpace {t} value)
  = ([(HoldSpace t, holdSpace)] ** Refl)
getAllVarsCommand (HoldApp holdSpace f) = ([] ** Refl)
getAllVarsCommand (FromHold holdSpace f) = ([] ** Refl)
getAllVarsCommand (ExecOnHold holdSpace f) = ([] ** Refl)
getAllVarsCommand (Routine {st} label sc) = ([(Label st, label)] ** Refl)
getAllVarsCommand (Call label) = ([] ** Refl)
getAllVarsCommand (IfThenElse f x y) = ([] ** Refl)
getAllVarsCommand (WithHoldContent holdSpace f) = ([] ** Refl)
getAllVarsCommand Quit = ([] ** Refl)
getAllVarsCommand Zap = ([] ** Refl)
getAllVarsCommand ZapFstLine = ([] ** Refl)
getAllVarsCommand ReadApp = ([] ** Refl)
getAllVarsCommand Put = ([] ** Refl)
getAllVarsCommand LineNumber = ([] ** Refl)
getAllVarsCommand NewCycle = ([] ** Refl)
getAllVarsCommand (ReadFrom x) = ([] ** Refl)
getAllVarsCommand (QueueRead x) = ([] ** Refl)
getAllVarsCommand PrintStd = ([] ** Refl)
getAllVarsCommand (WriteTo f) = ([] ** Refl)
getAllVarsCommand (WriteLineTo f) = ([] ** Refl)
getAllVarsCommand (ClearFile f) = ([] ** Refl)
getAllVarsCommand FileName = ([] ** Refl)

record VMState (sx : Variables) (io : FileScriptType) where
  constructor MkVMState
  patternSpace : String
  resultSpace : SnocList String
  store : LinkedListStore sx io

init : String -> VMState [<] st
init str = MkVMState str [<] empty

lift : (LinkedListStore sx io -> LinkedListStore sx' io')
    -> (VMState sx io -> VMState sx' io')
lift f (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace
              , resultSpace
              , store = f store }

put : String -> VMState sx io -> VMState sx io
put str (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = str
              , resultSpace
              , store }

deletePrefixLine : String -> String
deletePrefixLine str = ?deletePrefixLine_rhs

namespace Scripts
  public export
  data Scripts : Variables -> FileScriptType -> Type where
    Just : Script sx io -> Scripts sx io
    Then : Script sx io -> {sy : Variables} -> Thinning sy sx
        -> Scripts sy io -> Scripts sx io

namespace FileScripts
  public export
  data FileScripts : Variables -> Variables -> FileScriptType -> Type where
    Just : FileScript sx io -> FileScripts sx sx io
    Then : FileScript sx io -> {sy : Variables} -> Thinning sy sx
        -> FileScripts sy sy' io -> FileScripts sx sy' io

record LineInfo where
  constructor MkLineInfo
  line : String
  lineNumber : Nat
  isLastLine : Bool

from : LineInfo -> String -> List String -> LineInfo
from (MkLineInfo _ lineNumber _) name []        
  = MkLineInfo name (S lineNumber) True
from (MkLineInfo _ lineNumber _) name (x :: xs)
  = MkLineInfo name (S lineNumber) False

initLI : LineInfo
initLI = MkLineInfo "" 0 False

addrCheck : Address -> LineInfo -> Bool
addrCheck addr li = ?addrCheck_rhs

data SimpleCommand : Command sx ys st io -> Type where
    IsReplace : SimpleCommand (Replace t)
    IsExec : SimpleCommand (Exec f)
    IsPrint : SimpleCommand (Print)
    IsCreateHold : SimpleCommand (CreateHold name v)
    IsHoldApp : SimpleCommand (HoldApp name {pos} f)
    IsFromHold : SimpleCommand (FromHold name f {pos})
    IsExecOnHold : SimpleCommand (ExecOnHold name f {pos})
    IsRoutine : SimpleCommand (Routine name routine)
    IsZap : SimpleCommand (Zap)
    IsZapFstLine : SimpleCommand (ZapFstLine)

isSimpleCommand : (cmd : Command sx ys st io)
                -> Either (SimpleCommand cmd) (Not $ SimpleCommand cmd)
isSimpleCommand cmd = ?isSimpleCommand_rhs

execSimpleCommand : (cmd : Command sx ys st Local) -> VMState sx Local
                  -> {auto 0 prf : SimpleCommand cmd}
                  -> VMState (sx <>< ys) Local
execSimpleCommand (Replace replace) {prf = IsReplace}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = performReplace patternSpace replace
              , resultSpace
              , store }
execSimpleCommand (Exec f) {prf = IsExec}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = f patternSpace
              , resultSpace
              , store }
execSimpleCommand Print {prf = IsPrint}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = ""
              , resultSpace = resultSpace :< patternSpace
              , store }
execSimpleCommand (CreateHold hs initVal) {prf = IsCreateHold}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace
              , resultSpace
              , store = holdSpace hs initVal store }
execSimpleCommand (HoldApp name f {pos}) {prf = IsHoldApp}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace
              , resultSpace
              , store = execOnHoldSpace pos store (\v => f v patternSpace) }
execSimpleCommand (FromHold name f {pos}) {prf = IsFromHold}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = f patternSpace (getHoldSpace pos store)
              , resultSpace
              , store }
execSimpleCommand (ExecOnHold name f {pos}) {prf = IsExecOnHold}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace
              , resultSpace
              , store = execOnHoldSpace pos store f }
execSimpleCommand (Routine name routine {st}) {prf = IsRoutine}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace
              , resultSpace
              , store = label name routine store}
execSimpleCommand Zap {prf = IsZap}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = ""
              , resultSpace
              , store }
execSimpleCommand ZapFstLine {prf = IsZapFstLine}
                  (MkVMState patternSpace resultSpace store)
  = MkVMState { patternSpace = deletePrefixLine patternSpace
              , resultSpace
              , store }

mutual
  export
  interpretWithFileScriptCommand : {sx : Variables}           -- those
                                -> {sy : Variables}
                                -> (cmd : Command sx ys LineByLine Local)
                                -> (curr : FileScripts (sx <>< ys) sy' Local)
                                -> (full : FileScript sy Local) -- four
                                -> (sc : Scripts sy Local)      -- could be
                                -> Thinning sy sy'             -- one data structure
                                -> List String
                                -> VMState sx Local
                                -> LineInfo
                                -> SnocList String
  interpretWithFileScriptCommand cmd curr full sc x strs y z
    = ?interpretWithFileScriptCommand_rhs

  interpretWithFileScript :  {sx : Variables}            --- those
                          -> {sy : Variables}
                          -> {sy' : Variables}
                          -> (curr : FileScripts sx sy' Local)
                          -> (full : FileScript sy Local) -- four
                          -> (sc : Scripts sy Local)      -- could be
                          -> Thinning sy sy'               -- one data structure
                          -> List String
                          -> VMState sx Local
                          -> LineInfo
                          -> SnocList String
  interpretWithFileScript (Just []) full sc tau [] vm _
    = interpretAux sc (lift (\s => thin s tau) vm)
  interpretWithFileScript (Just []) full sc tau (l :: ln) vm li
    = interpretWithFileScript (Just full) full sc (id sy) ln
        (put l (lift (\s => thin s tau) vm)) (from li l ln)
  interpretWithFileScript (Just ((> cmd) :: fsc'))
                          full sc tau strs vm li with (getAllVarsCommand cmd)
    interpretWithFileScript (Just ((> cmd) :: fsc'))
                            full sc tau strs vm li | (ys ** Refl)
      = interpretWithFileScriptCommand
          cmd (Just fsc') full sc (dropLast _ ys . tau) strs vm li 
  interpretWithFileScript (Just ((addr ?> cmd) :: fsc'))
                          full sc tau strs vm li
    = if (addrCheck addr li)
      then interpretWithFileScriptCommand
            cmd (Just fsc') full sc tau strs vm li
      else interpretWithFileScript
            (Just fsc') full sc tau strs vm li
  interpretWithFileScript (Then [] tau' fsc {sy = sy'}) full sc tau lines vm li
    = interpretWithFileScript fsc full sc tau
                              lines (lift (\s => thin s tau') vm) li
  interpretWithFileScript (Then ((> cmd) :: fsc') tau' fsc)
                          full sc tau strs vm li with (getAllVarsCommand cmd)
    interpretWithFileScript (Then ((> cmd) :: fsc') tau' fsc)
                            full sc tau strs vm li | (ys ** Refl)
      = interpretWithFileScriptCommand
          cmd (Then fsc' (dropLast _ ys . tau') fsc)
          full sc tau strs vm li
  interpretWithFileScript (Then ((addr ?> cmd) :: fsc') tau' fsc)
                          full sc tau strs vm li
    = if (addrCheck addr li)
      then interpretWithFileScriptCommand
            cmd (Then fsc' tau' fsc) full sc tau strs vm li 
      else interpretWithFileScript (Then fsc' tau' fsc) full sc tau strs vm li 

  export
  interpretWithCommand : {sx : Variables}
                      -> {ys : List Variable}
                      -> (cmd : Command sx ys Total Local)
                      -> (sc : Scripts (sx <>< ys) Local)
                      -> VMState sx Local
                      -> SnocList String
  interpretWithCommand cmd sc vm {sx} with (isSimpleCommand cmd)
    interpretWithCommand cmd sc vm | (Left prf)
      = interpretAux sc (execSimpleCommand cmd vm)
    interpretWithCommand (Replace x) sc vm    | (Right f) = absurd (f IsReplace)
    interpretWithCommand (Exec _) _ _         | (Right f) = absurd (f IsExec)
    interpretWithCommand Print _ _            | (Right f) = absurd (f IsPrint)
    interpretWithCommand (CreateHold _ _) _ _ | (Right f) = absurd (f IsCreateHold)
    interpretWithCommand (Routine _ _) _ _    | (Right f) = absurd (f IsRoutine)
    interpretWithCommand (HoldApp _ _) _ _    | (Right f) = absurd (f IsHoldApp)
    interpretWithCommand (FromHold _ _) _ _   | (Right f) = absurd (f IsFromHold)
    interpretWithCommand (ExecOnHold _ _) _ _ | (Right f) = absurd (f IsExecOnHold)
    interpretWithCommand Quit _ vm | _ = vm.resultSpace
    interpretWithCommand (IfThenElse f sc1 sc2) sc vm {sx} | _
      = if (f vm.patternSpace)
        then interpretAux (Then sc1 (id sx) sc) vm
        else interpretAux (Then sc2 (id sx) sc) vm
    interpretWithCommand (Call _ {pos}) sc vm {sx} | _
      = let r := getRoutine sx pos vm.store
        in interpretAux (Then r (id sx) sc) vm
    interpretWithCommand (WithHoldContent _ f {pos}) sc vm {sx} | _
      = let sc' := thin (f $ getHoldSpace pos vm.store) (dropElem sx pos)
        in interpretAux (Then sc' (id sx) sc) vm

  export
  interpretAux : {sx : Variables} -> (sc : Scripts sx Local)
              -> VMState sx Local -> SnocList String
  interpretAux (Just []) vm = vm.resultSpace
  interpretAux {sx} (Just ((ln *> fsc) :: sc)) vm
    = interpretWithFileScript (Just []) fsc (Just sc) (id sx) ln vm initLI
  interpretAux (Just ((|> cmd) :: sc)) vm {sx} with (getAllVarsCommand cmd)
    interpretAux (Just ((|> cmd) :: sc)) vm {sx} | (ys ** Refl)
      = interpretWithCommand cmd (Just sc) vm 
  interpretAux (Then [] tau scCont) vm
    = interpretAux scCont (lift (\s => thin s tau) vm)
  interpretAux {sx} (Then ((ln *> fsc) :: sc) tau scCont) vm
    = interpretWithFileScript (Just []) fsc (Then sc tau scCont) (id sx) ln vm initLI
  interpretAux (Then ((|> cmd) :: sc) tau scCont) vm {sx} with (getAllVarsCommand cmd)
    interpretAux (Then ((|> cmd) :: sc) tau scCont) vm {sx} | (ys ** Refl)
      = interpretWithCommand cmd (Then sc (dropLast sx ys . tau) scCont) vm

export
interpret : (sc : Script [<] Local) -> String -> SnocList String
interpret sc str = interpretAux (Just sc) (init str)

export
interpretIO : (sc : Script [<] st) -> String -> IO (Either String (List String))
