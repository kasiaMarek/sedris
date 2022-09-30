module Sedris

import public Sedris.Lang
import public Sedris.Replace
import public Sedris.Extra
import public Sedris.VariableStore

import Data.DPair

getAllVarsCommand : Command sx ys st io -> List Variable
getAllVarsCommand (Replace x) = []
getAllVarsCommand (Exec f) = []
getAllVarsCommand Print = []
getAllVarsCommand (CreateHold holdSpace {t} value) = [(HoldSpace t, holdSpace)]
getAllVarsCommand (HoldApp holdSpace f) = []
getAllVarsCommand (FromHold holdSpace f) = []
getAllVarsCommand (ExecOnHold holdSpace f) = []
getAllVarsCommand (Routine {st} label sc) = [(Label st, label)]
getAllVarsCommand (Call label) = []
getAllVarsCommand (IfThenElse f x y) = []
getAllVarsCommand (WithHoldContent holdSpace f) = []
getAllVarsCommand Quit = []
getAllVarsCommand Zap = []
getAllVarsCommand ZapFstLine = []
getAllVarsCommand ReadApp = []
getAllVarsCommand Put = []
getAllVarsCommand LineNumber = []
getAllVarsCommand NewCycle = []
getAllVarsCommand (ReadFrom x) = []
getAllVarsCommand (QueueRead x) = []
getAllVarsCommand PrintStd = []
getAllVarsCommand (WriteTo f) = []
getAllVarsCommand (WriteLineTo f) = []
getAllVarsCommand (ClearFile f) = []
getAllVarsCommand FileName = []

getAllVarsFileScript : FileScript sx t -> List Variable
getAllVarsFileScript [] = []
getAllVarsFileScript ((> cmd ) :: fsc)
  = getAllVarsCommand cmd ++ getAllVarsFileScript fsc
getAllVarsFileScript ((_ ?> _) :: fsc) = getAllVarsFileScript fsc
getAllVarsFileScript ((_ ?: _) :: fsc) = getAllVarsFileScript fsc

getAllVars : Script sx t -> List Variable
getAllVars [] = []
getAllVars ((_ *  _) :: sc)  = getAllVars sc
getAllVars ((|*>  _) :: sc)  = getAllVars sc
getAllVars ((_ *> _) :: sc)  = getAllVars sc
getAllVars ((|> cmd) :: sc)  = getAllVarsCommand cmd ++ getAllVars sc

----------
record VMState (sx : Variables) (st : FileScriptType) where
  constructor MkVMState
  patternSpace : String
  resultSpace : SnocList String
  store : LinkedListStore sx st
  vars : Variables
  0 varsPrf : vars = sx

init : String -> VMState [<] st
init str = MkVMState str [<] empty [<] Refl

lift : (sx' : Variables)
    -> (LinkedListStore sx st -> LinkedListStore sx' st')
    -> (VMState sx st -> VMState sx' st')
lift sx' f (MkVMState patternSpace resultSpace store vars Refl)
  = MkVMState { patternSpace
              , resultSpace
              , store = f store
              , vars = sx'
              , varsPrf = Refl }

------
deletePrefixLine : String -> String

mutual
  interpretCommand : {st : ScriptType}
                  -> (cmd : Command sx ys st Local)
                  -> VMState sx Local
                  -> Either (SnocList String)
                            (VMState (sx <>< ys) Local) -- left if we quit mid-exec
  interpretCommand  (Replace replace)
                    (MkVMState patternSpace resultSpace store vars Refl)
    = Right $ MkVMState { patternSpace = performReplace patternSpace replace
                        , resultSpace
                        , store
                        , vars
                        , varsPrf = Refl }
  interpretCommand  (Exec f)
                    (MkVMState patternSpace resultSpace store vars Refl)
    = Right $ MkVMState { patternSpace = f patternSpace
                        , resultSpace
                        , store
                        , vars
                        , varsPrf = Refl }
  interpretCommand  Print
                    (MkVMState patternSpace resultSpace store vars Refl)
    = Right $ MkVMState { patternSpace = ""
                        , resultSpace = resultSpace :< patternSpace
                        , store
                        , vars
                        , varsPrf = Refl }
  interpretCommand  (CreateHold hs {t} initVal)
                    (MkVMState patternSpace resultSpace store vars Refl)
    = Right $ MkVMState { patternSpace
                        , resultSpace
                        , store = holdSpace hs initVal store
                        , vars = vars :< (HoldSpace t, hs)
                        , varsPrf = Refl}
  interpretCommand  (HoldApp holdSpace f {pos})
                    (MkVMState patternSpace resultSpace store vars Refl)
    = Right $ MkVMState { patternSpace
                    , resultSpace
                    , store =
                        execOnHoldSpace pos store (\v => f v patternSpace)
                    , vars
                    , varsPrf = Refl}
  interpretCommand  (FromHold holdSpace f {pos})
                    (MkVMState patternSpace resultSpace store vars Refl)
    = Right $ MkVMState { patternSpace
                            = f patternSpace (getHoldSpace pos store)
                        , resultSpace
                        , store
                        , vars
                        , varsPrf = Refl }
  interpretCommand  (ExecOnHold holdSpace f {pos})
                    (MkVMState patternSpace resultSpace store vars Refl)
    = Right $ MkVMState { patternSpace
                        , resultSpace
                        , store = execOnHoldSpace pos store f
                        , vars
                        , varsPrf = Refl}
  interpretCommand  (Call label {pos})
                    (MkVMState patternSpace resultSpace store vars Refl)
    = ?iodej
      {-
      let Evidence sx' (sc, hs, f) := getRoutine pos store
      in map  (lift $ f . (\x => trim x (length hs) {ford = lengthPrf hs}))
              (interpretAux sc (MkVMState patternSpace resultSpace hs))
      -}
  interpretCommand  (WithHoldContent holdSpace f {pos})
                    (MkVMState patternSpace resultSpace store vars Refl) {st}
    = case st of
        Total =>
          let script := thin (f $ getHoldSpace pos store) (dropElem vars pos)
          in map  (lift vars (\s => thin s (dropLast vars (getAllVars script))))
                  (interpretAux script
                      (MkVMState patternSpace resultSpace store vars Refl))
        LineByLine => ?dneiwon_1
  interpretCommand  Quit
                    (MkVMState patternSpace resultSpace store vars Refl)
    = Left $ resultSpace
  interpretCommand  (Routine name sc)
                    (MkVMState patternSpace resultSpace store vars Refl) {st}
    = Right $ MkVMState { patternSpace
                        , resultSpace
                        , store = label name sc store
                        , vars = vars :< (Label st, name)
                        , varsPrf = Refl}
  interpretCommand  (IfThenElse f sc1 sc2) {sx = vars}
                    (MkVMState patternSpace resultSpace store vars Refl) {st}
    = case st of
        Total =>
          if (f patternSpace)
          then map  (lift vars (\s => thin s (dropLast vars (getAllVars sc1))))
                    (interpretAux sc1
                        (MkVMState patternSpace resultSpace store vars Refl))
          else map  (lift vars (\s => thin s (dropLast vars (getAllVars sc2))))
                    (interpretAux sc2
                        (MkVMState patternSpace resultSpace store vars Refl))
        LineByLine => ?ndieowh
  interpretCommand Zap (MkVMState patternSpace resultSpace store vars Refl)
    = Right $ MkVMState { patternSpace = ""
                        , resultSpace
                        , store
                        , vars
                        , varsPrf = Refl}
  interpretCommand  ZapFstLine
                    (MkVMState patternSpace resultSpace store vars Refl)
    = Right $ MkVMState { patternSpace = deletePrefixLine patternSpace
                        , resultSpace
                        , store
                        , vars
                        , varsPrf = Refl}
  interpretCommand  ReadApp
                    (MkVMState patternSpace resultSpace store vars Refl)
    = ?interpretCommand_missing_case_7
  interpretCommand  Put
                    (MkVMState patternSpace resultSpace store vars Refl)
    = ?interpretCommand_missing_case_8
  interpretCommand  LineNumber
                    (MkVMState patternSpace resultSpace store vars Refl)
    = ?interpretCommand_missing_case_9
  interpretCommand  NewCycle
                    (MkVMState patternSpace resultSpace store vars Refl)
    = ?interpretCommand_missing_case_10
  interpretCommand  (ReadFrom f) vm
    = ?interpretCommand_missing_case_11
  interpretCommand  (QueueRead f) vm
    = ?interpretCommand_missing_case_12

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
  interpretFileScript fsc (l :: tail) vm = ?nioew
    -- = interpretFileScriptForLine fsc vm l
    --     >>= ( interpretFileScript fsc tail
    --         . (lift $ ?thining_3))

  export
  interpretAux : (sc : Script sx Local)
              -> VMState sx Local
              -> Either (SnocList String)
                        (VMState (sx <>< getAllVars sc) Local)
  interpretAux [] vm = Right vm
  interpretAux ((strs *> fsc) :: sc) vm
    = interpretFileScript fsc strs vm >>= interpretAux sc
  interpretAux ((::) (|> cmd) sc) vmSt
    = interpretCommand cmd vmSt
      >>= (\vm  => map (\res =>
                        replace {p = (\x => VMState x Local)} ?ncjwkl res)
                      (interpretAux sc vm))

export
interpret : (sc : Script [<] Local) -> String -> SnocList String
interpret sc str = ?nceiown
  -- let Evidence (MkVMState _ resultSpace _) := interpretAux sc (init str)
  -- in resultSpace

export
interpretIO : (sc : Script [<] st) -> String -> IO (Either String (List String))
