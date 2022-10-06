module Sedris.Interpret

import public Sedris.Lang
import Sedris.Replace
import Sedris.Thinnings
import Sedris.VariableStore

import public Data.Regex
import Data.DPair

record VMState (sx : Variables) (io : FileScriptType) where
  constructor MkVMState
  patternSpace : String
  resultSpace : SnocList String
  store : LinkedListStore sx io

export
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
deletePrefixLine str
  = case (lines str) of
      [] => ""
      (h :: tail) => unlines tail

namespace Scripts
  public export
  data Scripts : Variables -> FileScriptType -> Type where
    Just : Script sx io -> Scripts sx io
    Then : Script sx io -> {sy : Variables} -> Weakening sy sx
        -> Scripts sy io -> Scripts sx io

namespace FileScripts
  public export
  data FileScripts : Variables -> Variables -> FileScriptType -> Type where
    Just : FileScript sx io -> {sy : Variables} -> Weakening sy sx
        -> Scripts sy io -> FileScripts sx sy io
    Then : FileScript sx io -> {sy : Variables} -> Weakening sy sx
        -> FileScripts sy sy' io -> FileScripts sx sy' io

getScript : FileScripts sx sy io
          -> (sy' : Variables ** (sy' = sy, Weakening sy' sx, Scripts sy' io))
getScript (Just fsc tau sc) = (sy ** (Refl, tau, sc))
getScript (Then fsc tau fscs) =
  let (sy' ** (Refl, tau', sc)) := getScript fscs
  in (sy' ** (Refl, tau . tau', sc))

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
addrCheck (Line n)         (MkLineInfo _ lineNum _)  = (n == lineNum)
addrCheck (Lines ns)       (MkLineInfo _ lineNum _)  = isJust $ find (== lineNum) ns
addrCheck (LineRange s l)  (MkLineInfo _ lineNum _)  = lineNum < l && lineNum >= s
addrCheck (RegexWhole re)  (MkLineInfo line _ _)     = match re line
addrCheck (RegexPrefix re) (MkLineInfo line _ _)     = isJust $ parsePrefix re line
addrCheck (RegexExists re) (MkLineInfo line _ _)     =
  case asDisjointMatches re line True of
    (Suffix _)   => False
    (Cons _ _ _) => True
addrCheck (Not addr)       li                        = not (addrCheck addr li)
addrCheck LastLine         (MkLineInfo _ _ lastLine) = lastLine

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
isSimpleCommand (Replace x) = Left IsReplace
isSimpleCommand (Exec f) = Left IsExec
isSimpleCommand Print = Left IsPrint
isSimpleCommand (CreateHold holdSpace x) = Left IsCreateHold
isSimpleCommand (HoldApp holdSpace f) = Left IsHoldApp
isSimpleCommand (FromHold holdSpace f) = Left IsFromHold
isSimpleCommand (ExecOnHold holdSpace f) = Left IsExecOnHold
isSimpleCommand (Routine label x) = Left IsRoutine
isSimpleCommand (Call label) = Right (\case _ impossible)
isSimpleCommand (IfThenElse f x y) = Right (\case _ impossible)
isSimpleCommand (WithHoldContent holdSpace f) = Right (\case _ impossible)
isSimpleCommand Quit = Right (\case _ impossible)
isSimpleCommand Zap = Left IsZap
isSimpleCommand ZapFstLine = Left IsZapFstLine
isSimpleCommand ReadApp = Right (\case _ impossible)
isSimpleCommand Put = Right (\case _ impossible)
isSimpleCommand LineNumber = Right (\case _ impossible)
isSimpleCommand NewCycle = Right (\case _ impossible)
isSimpleCommand (ReadFrom x) = Right (\case _ impossible)
isSimpleCommand (QueueRead x) = Right (\case _ impossible)
isSimpleCommand PrintStd = Right (\case _ impossible)
isSimpleCommand (WriteTo f) = Right (\case _ impossible)
isSimpleCommand (WriteLineTo f) = Right (\case _ impossible)
isSimpleCommand (ClearFile f) = Right (\case _ impossible)
isSimpleCommand FileName = Right (\case _ impossible)

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
  interpretFSCmd : {sx : Variables}
                -> {ys : List Variable}
                -> {0 sy : Variables}
                -> (cmd : Command sx ys LineByLine Local)
                -> (curr : FileScripts (sx <>< ys) sy Local)
                -> (full : FileScript sy Local)
                -> List String
                -> VMState sx Local
                -> LineInfo
                -> SnocList String
  interpretFSCmd cmd curr full lines vm li with (isSimpleCommand cmd)
    interpretFSCmd cmd curr full lines vm li | Left prf =
      interpretFS curr full lines (execSimpleCommand cmd vm) li
    interpretFSCmd (Replace _)      _ _ _ _ _ | Right f = absurd (f IsReplace)
    interpretFSCmd (Exec _)         _ _ _ _ _ | Right f = absurd (f IsExec)
    interpretFSCmd Print            _ _ _ _ _ | Right f = absurd (f IsPrint)
    interpretFSCmd (CreateHold _ _) _ _ _ _ _ | Right f = absurd (f IsCreateHold)
    interpretFSCmd (HoldApp _ _)    _ _ _ _ _ | Right f = absurd (f IsHoldApp)
    interpretFSCmd (FromHold _ _)   _ _ _ _ _ | Right f = absurd (f IsFromHold)
    interpretFSCmd (ExecOnHold _ _) _ _ _ _ _ | Right f = absurd (f IsExecOnHold)
    interpretFSCmd (Routine _ _)    _ _ _ _ _ | Right f = absurd (f IsRoutine)
    interpretFSCmd Zap              _ _ _ _ _ | Right f = absurd (f IsZap)
    interpretFSCmd ZapFstLine       _ _ _ _ _ | Right f = absurd (f IsZapFstLine)
    interpretFSCmd Quit curr full lines vm li | _ = vm.resultSpace
    interpretFSCmd (IfThenElse f sc1 sc2) curr full lines vm li | _ =
      if f vm.patternSpace
      then interpretFS (Then sc1 id curr) full lines vm li
      else interpretFS (Then sc2 id curr) full lines vm li
    interpretFSCmd (Call _ {pos}) curr full lines vm li | _ =
      let r := getRoutine sx pos vm.store
      in interpretFS (Then r id curr) full lines vm li
    interpretFSCmd (WithHoldContent _ f {pos}) curr full lines vm li | _
      = interpretFS (Then (f $ getHoldSpace pos vm.store) id curr)
                    full lines vm li
    interpretFSCmd ReadApp curr full [] vm li | _ =
      let (sy ** (Refl, tau, sc)) = getScript curr
      in interpretS sc (lift (\s => weaken s tau) vm)
    interpretFSCmd ReadApp curr full (l :: ln)
                   (MkVMState patternSpace resultSpace store) li | _ =
      interpretFS curr full ln
                  (MkVMState (l ++ "\n" ++ patternSpace) resultSpace store)
                  (from li l ln)
    interpretFSCmd Put curr full [] vm li | _ =
      let (sy ** (Refl, tau, sc)) = getScript curr
      in interpretS sc (lift (\s => weaken s tau) vm)
    interpretFSCmd Put curr full (l :: ln) vm li | _ =
      interpretFS curr full ln (put l vm) (from li l ln)
    interpretFSCmd LineNumber curr full lines
                   (MkVMState patternSpace resultSpace store)
                   li@(MkLineInfo _ lineNum _) | _ =
      interpretFS curr full lines
                  (MkVMState patternSpace (resultSpace :< show lineNum) store) li
    interpretFSCmd NewCycle curr full ln vm li | _ =
      let (sy ** (Refl, tau, sc)) = getScript curr
      in case ln of
          [] => interpretS sc (lift (\s => weaken s tau) vm)
          (l :: ln) =>
            interpretFS (Just full id sc) full ln
              (put l (lift (\s => weaken s tau) vm)) (from li l ln)
    interpretFSCmd (ReadFrom lns) curr full lines vm li | _ =
      interpretFS curr full lns vm li
    interpretFSCmd (QueueRead lns) curr full lines vm li | _ =
      interpretFS curr full (lines ++ lns) vm li

  interpretFS :  {sx : Variables}
              -> (curr : FileScripts sx sy Local)
              -> (full : FileScript sy Local)
              -> List String
              -> VMState sx Local
              -> LineInfo
              -> SnocList String
  interpretFS (Just [] tau sc) full [] vm _
    = interpretS sc (lift (\s => weaken s tau) vm)
  interpretFS (Just [] tau sc) full (l :: ln) vm li
    = interpretFS (Just full id sc) full ln
        (put l (lift (\s => weaken s tau) vm)) (from li l ln)
  interpretFS (Just ((> cmd) :: fsc') tau sc)
                          full strs vm li with (extractNewVars cmd)
    interpretFS (Just ((> cmd) :: fsc') tau sc)
                            full strs vm li | (ys ** Refl)
      = interpretFSCmd
          cmd (Just fsc' (Weaken ys . tau) sc) full strs vm li 
  interpretFS (Just ((addr ?> cmd) :: fsc') tau sc)
                          full strs vm li
    = if (addrCheck addr li)
      then interpretFSCmd
            cmd (Just fsc' tau sc) full strs vm li
      else interpretFS
            (Just fsc' tau sc) full strs vm li
  interpretFS (Then [] tau' fsc {sy = sy'}) full lines vm li
    = interpretFS fsc full
                              lines (lift (\s => weaken s tau') vm) li
  interpretFS (Then ((> cmd) :: fsc') tau' fsc)
                          full strs vm li with (extractNewVars cmd)
    interpretFS (Then ((> cmd) :: fsc') tau' fsc)
                            full strs vm li | (ys ** Refl)
      = interpretFSCmd
          cmd (Then fsc' (Weaken ys . tau') fsc)
          full strs vm li
  interpretFS (Then ((addr ?> cmd) :: fsc') tau' fsc)
                          full strs vm li
    = if (addrCheck addr li)
      then interpretFSCmd
            cmd (Then fsc' tau' fsc) full strs vm li 
      else interpretFS (Then fsc' tau' fsc) full strs vm li 

  export
  interpretCmd : {sx : Variables}
              -> {ys : List Variable}
              -> (cmd : Command sx ys Total Local)
              -> (sc : Scripts (sx <>< ys) Local)
              -> VMState sx Local
              -> SnocList String
  interpretCmd cmd sc vm {sx} with (isSimpleCommand cmd)
    interpretCmd cmd sc vm | (Left prf)
      = interpretS sc (execSimpleCommand cmd vm)
    interpretCmd (Replace x) sc vm    | (Right f) = absurd (f IsReplace)
    interpretCmd (Exec _) _ _         | (Right f) = absurd (f IsExec)
    interpretCmd Print _ _            | (Right f) = absurd (f IsPrint)
    interpretCmd (CreateHold _ _) _ _ | (Right f) = absurd (f IsCreateHold)
    interpretCmd (Routine _ _) _ _    | (Right f) = absurd (f IsRoutine)
    interpretCmd (HoldApp _ _) _ _    | (Right f) = absurd (f IsHoldApp)
    interpretCmd (FromHold _ _) _ _   | (Right f) = absurd (f IsFromHold)
    interpretCmd (ExecOnHold _ _) _ _ | (Right f) = absurd (f IsExecOnHold)
    interpretCmd Quit _ vm | _ = vm.resultSpace
    interpretCmd (IfThenElse f sc1 sc2) sc vm {sx} | _
      = if (f vm.patternSpace)
        then interpretS (Then sc1 id sc) vm
        else interpretS (Then sc2 id sc) vm
    interpretCmd (Call _ {pos}) sc vm {sx} | _
      = let r := getRoutine sx pos vm.store
        in interpretS (Then r id sc) vm
    interpretCmd (WithHoldContent _ f {pos}) sc vm {sx} | _
      = interpretS (Then (f $ getHoldSpace pos vm.store) id sc) vm

  export
  interpretS : {sx : Variables} -> (sc : Scripts sx Local)
            -> VMState sx Local -> SnocList String
  interpretS (Just []) vm = vm.resultSpace
  interpretS {sx} (Just ((ln *> fsc) :: sc)) vm
    = interpretFS (Just [] id (Just sc)) fsc ln vm initLI
  interpretS (Just ((|> cmd) :: sc)) vm {sx} with (extractNewVars cmd)
    interpretS (Just ((|> cmd) :: sc)) vm {sx} | (ys ** Refl)
      = interpretCmd cmd (Just sc) vm 
  interpretS (Then [] tau scCont) vm
    = interpretS scCont (lift (\s => weaken s tau) vm)
  interpretS {sx} (Then ((ln *> fsc) :: sc) tau scCont) vm
    = interpretFS (Just [] id (Then sc tau scCont)) fsc ln vm initLI
  interpretS (Then ((|> cmd) :: sc) tau scCont) vm {sx} with (extractNewVars cmd)
    interpretS (Then ((|> cmd) :: sc) tau scCont) vm {sx} | (ys ** Refl)
      = interpretCmd cmd (Then sc (Weaken ys . tau) scCont) vm

export
interpretIO : (sc : Script [<] st) -> String -> IO (Either String (List String))
