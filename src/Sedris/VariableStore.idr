module Sedris.VariableStore

import Sedris.Lang
import Data.Void

public export
Variable : Type
Variable = (VarType, String)

public export
Variables : Type
Variables = SnocList Variable

export
extractNewVars : Command sx ys st io -> (vars : List Variable ** vars = ys)
extractNewVars (Replace x) = ([] ** Refl)
extractNewVars (Exec f) = ([] ** Refl)
extractNewVars Print = ([] ** Refl)
extractNewVars (CreateHold holdSpace {t} value)
  = ([(HoldSpace t, holdSpace)] ** Refl)
extractNewVars (HoldApp holdSpace f) = ([] ** Refl)
extractNewVars (FromHold holdSpace f) = ([] ** Refl)
extractNewVars (ExecOnHold holdSpace f) = ([] ** Refl)
extractNewVars (Routine {st} label sc) = ([(Label st, label)] ** Refl)
extractNewVars (Call label) = ([] ** Refl)
extractNewVars (IfThenElse f x y) = ([] ** Refl)
extractNewVars (WithHoldContent holdSpace f) = ([] ** Refl)
extractNewVars Quit = ([] ** Refl)
extractNewVars Zap = ([] ** Refl)
extractNewVars ZapFstLine = ([] ** Refl)
extractNewVars ReadApp = ([] ** Refl)
extractNewVars Put = ([] ** Refl)
extractNewVars LineNumber = ([] ** Refl)
extractNewVars NewCycle = ([] ** Refl)
extractNewVars (ReadFrom x) = ([] ** Refl)
extractNewVars (QueueRead x) = ([] ** Refl)
extractNewVars PrintStd = ([] ** Refl)
extractNewVars (WriteTo f) = ([] ** Refl)
extractNewVars (WriteLineTo f) = ([] ** Refl)
extractNewVars (ClearFile f) = ([] ** Refl)
extractNewVars FileName = ([] ** Refl)

data Weakening : Variables -> Variables -> Type where
  Weaken : (xs : List Variable) -> {auto 0 ford : sy = sx <>< xs}
    -> Weakening sx sy

public export
data Thinning : Variables -> Variables -> Type where
  Lin : Thinning [<] sx
  (.Keep) : Thinning sx sy -> Thinning (sx :< y) (sy :< y)
  (.Drop) : Thinning sx sy -> Thinning  sx       (sy :< y)

0 uninhabited' : {sx, sy : Variables} -> {y : Variable}
              -> Thinning (sx ++ (sy :< y)) sx -> Void
uninhabited' {sx = _, sy = [<], y} tau.Keep = uninhabited' tau {sy = [<]}
uninhabited' {sx = _, sy = [<], y} (tau.Drop {sy = sy', y = y'}) = uninhabited' tau {sy = [< y'],y, sx = sy'}
uninhabited' {sx = _, sy = (sy :< x), y} (tau.Keep {sy = sy'}) =
  uninhabited'  (replace {p = (\e => Thinning (e :< x) sy')} 
                          (sym $ appendAssociative _ _ _)
                          tau)
                {sx = sy', sy = ([< y] ++ sy), y = x}
uninhabited' {sx = _, sy = (sy :< x), y} (tau.Drop {sy = sy', y = y'}) =
  uninhabited'  (replace {p = (\e => Thinning (e :< x :< y) sy')} 
                          (sym $ appendAssociative _ _ _)
                          tau)
                {sx = sy', sy = ([< y'] ++ sy) :< x}

export
Uninhabited (Thinning (sx :< x) sx) where
  uninhabited tau = absurdity (uninhabited' tau {sy = [<]})

-- Smart constructors
(:<) : Thinning sx sy -> (keep : Bool) ->
  Thinning (ifThenElse keep (sx :< y) sx) (sy :< y)
tau :< False = tau.Drop
tau :< True = tau.Keep

I,O : Bool
I = True
O = False

export
id : (sx : Variables) -> Thinning sx sx
id [<] = [<]
id (sx :< x) = (id sx).Keep

export
(.) : Thinning sy sz -> Thinning sx sy -> Thinning sx sz
(.) tau [<]                     {sy = sy,        sz = sz,        sx = [<]      }
  = Lin
(.) tau.Keep tau'.Keep          {sy = (sy :< y), sz = (sy :< y), sx = (sx :< y)}
  = (tau . tau').Keep
(.) tau.Drop tau'.Keep          {sy = (sy :< y), sz = (sy :< y), sx = (sx :< y)}
  = (tau . (tau'.Drop)).Keep
(.) tau.Keep tau'.Drop          {sy = (sy :< y), sz = (sy :< y), sx = sx       }
  = (tau . tau').Drop
(.) tau.Drop tau'.Drop          {sy = (sy :< y), sz = (sy :< y), sx = sx       }
  = (tau . (tau'.Drop)).Drop

keepLastAux : (ys : List Variable)
            -> Thinning sx sx'
            -> Thinning (sx <>< ys) (sx' <>< ys)
keepLastAux [] tau = tau
keepLastAux (y :: ys) tau = keepLastAux ys tau.Keep

export
keepLast : (sx : Variables)
        -> (ys : List Variable)
        -> Thinning (sx <>< ys) (sx <>< ys)
keepLast sx ys = keepLastAux ys (id sx)

-- id is neutral, (.) associative, i.e. a category whose objects are
-- Variables values and morphisms are thinnings

namespace Position
  public export
  thin : x `Elem` sx -> Thinning sx sy -> x `Elem` sy
  thin _ [<] impossible
  thin Here (tau.Keep) = Here
  thin (There pos) (tau.Keep) = There (pos `thin` tau)
  thin pos (tau .Drop) = There (pos `thin` tau)

mutual
  namespace Cmd
    public export
    thin : Command sx zs st io -> Thinning sx sy -> Command sy zs st io
    thin (Replace x) tau = Replace x
    thin (Exec f) tau = Exec f
    thin Print tau = Print
    thin (CreateHold hs x) tau = CreateHold hs x
    thin (HoldApp hs f {pos}) tau = HoldApp hs f {pos = pos `thin` tau}
    thin (FromHold hs f {pos}) tau = FromHold hs f {pos = pos `thin` tau}
    thin (ExecOnHold hs f {pos}) tau = ExecOnHold hs f {pos = pos `thin` tau}
    thin (Routine label r {st = Total}) tau = Routine label (r `thin` tau)
    thin (Routine label r {st = LineByLine}) tau = Routine label (r `thin` tau)
    thin (Call label {pos}) tau = Call label {pos = pos `thin` tau}
    thin (IfThenElse f sc1 sc2 {st = Total}) tau =
      IfThenElse f (sc1 `thin` tau) (sc2 `thin` tau)
    thin (IfThenElse f sc1 sc2 {st = LineByLine}) tau =
      IfThenElse f (sc1 `thin` tau) (sc2 `thin` tau)
    thin (WithHoldContent holdSpace f {pos = pos} {st = Total}) tau =
      WithHoldContent holdSpace (\v => (f v) `thin` tau) {pos = pos `thin` tau}
    thin (WithHoldContent holdSpace f {pos = pos} {st = LineByLine}) tau =
      WithHoldContent holdSpace (\v => (f v) `thin` tau) {pos = pos `thin` tau}
    thin Quit tau = Quit
    thin Zap tau = Zap
    thin ZapFstLine tau = ZapFstLine
    thin ReadApp tau = ReadApp
    thin Put tau = Put
    thin LineNumber tau = LineNumber
    thin NewCycle tau = NewCycle
    thin (ReadFrom fl) tau = ReadFrom fl
    thin (QueueRead fl) tau = QueueRead fl
    thin PrintStd tau = PrintStd
    thin (WriteTo fl) tau = WriteTo fl
    thin (WriteLineTo fl) tau = WriteLineTo fl
    thin (ClearFile fl) tau = ClearFile fl
    thin FileName tau = FileName

  namespace FileScript
    public export
    thin : FileScript xs io -> Thinning xs ys -> FileScript ys io
    thin [] tau = []
    thin ((> cmd) :: fsc) tau =
      let (ys' ** Refl) := extractNewVars cmd
      in ((> (cmd `thin` tau)) :: (fsc `thin` (keepLastAux ys' tau)))
    thin ((addr ?> cmd) :: fsc) tau
      = ((addr ?> (cmd `thin` tau)) :: (fsc `thin` tau))

  namespace Script
    public export
    thin : Script xs io -> Thinning xs ys -> Script ys io
    thin [] tau = []
    thin ((fl * fsc) :: cmds) tau
      = ((fl * (fsc `thin` tau)) :: (cmds `thin` tau))
    thin ((|*> fsc) :: cmds) tau
      = ((|*> (fsc `thin` tau)) :: (cmds `thin` tau))
    thin ((strs *> fsc) :: cmds) tau
      = ((strs *> (fsc `thin` tau)) :: (cmds `thin` tau))
    thin ((|> cmd) :: cmds) tau =
      let (ys' ** Refl) := extractNewVars cmd
      in ((|> (cmd `thin` tau)) :: (cmds `thin` (keepLastAux ys' tau)))

namespace TailThinning
  public export
  data IsTailThinning : Thinning sx sy -> Type where
    IsId    : {tau : Thinning sx sx} -> IsTailThinning tau
    IsDrop : IsTailThinning tau -> IsTailThinning (tau.Drop)

  public export
  TailThinning : Variables -> Variables -> Type
  TailThinning sx sy = Thinning sx sy `DPair` IsTailThinning

  export
  thin : Script xs io -> TailThinning xs ys -> Script ys io
  thin sc (tau ** _) = thin sc tau

  export
  id : (sx : Variables) -> TailThinning sx sx
  id sx = ((id sx) ** IsId)

  dropLastAux : (ys : List Variable)
            -> TailThinning sx sx'
            -> TailThinning sx (sx' <>< ys)
  dropLastAux [] tau = tau
  dropLastAux (y :: ys) (tau ** isTail) =
    dropLastAux ys ((tau.Drop) ** (IsDrop isTail))

  export
  dropLast : (sx : Variables)
          -> (ys : List Variable)
          -> TailThinning sx (sx <>< ys)
  dropLast sx ys = dropLastAux ys (id sx)

  export
  (.) : TailThinning sy sz -> TailThinning sx sy -> TailThinning sx sz


public export
interface VariableStore (Store : Variables -> FileScriptType -> Type) where
  --- adding variables
  holdSpace : (name : String) -> {t : Type} -> (value : t) -> Store sx st
            -> Store (sx :< (HoldSpace t, name)) st
  label : (name : String) -> {st : ScriptType} -> (getScriptByType st sx io)
        -> Store sx io -> Store (sx :< (Label st, name)) io
  --- getting variables
  getHoldSpace : {0 name : String} -> {0 t : Type} -> {0 sx : Variables}
              -> (pos : (HoldSpace t, name) `Elem` sx)
              -> Store sx st -> t
  getRoutine : {0 name : String}
            -> (sx : Variables)
            -> {st : ScriptType}
            -> (pos : (Label st, name) `Elem` sx)
            -> Store sx io
            -> getScriptByType st sx io
  --- variable mutation
  execOnHoldSpace : {0 name : String} -> {0 t : Type}
                  -> {0 sx : Variables} -> (pos : (HoldSpace t, name) `Elem` sx)
                  -> Store sx st -> (t -> t)
                  -> Store sx st
  --- thinning
  thin : Store sy st -> TailThinning sx sy -> Store sx st
  --- empty store
  empty : Store [<] st

namespace LinkedListStore
  public export
  data LinkedListStore : Variables -> FileScriptType -> Type where
    Empty : LinkedListStore [<] st
    HS : (name : String) -> {t : Type} -> (value : t) -> LinkedListStore sx st
      -> LinkedListStore (sx :< (HoldSpace t, name)) st
    LB : (name : String) -> {st : ScriptType} -> (getScriptByType st sx io)
      -> LinkedListStore sx io
      -> LinkedListStore (sx :< (Label st, name)) io
  
  getHoldSpace : {0 name : String} -> {0 t : Type}
              -> {0 xs : SnocList (VarType, String)}
              -> (pos : (HoldSpace t, name) `Elem` xs)
              -> LinkedListStore xs st
              -> t
  getHoldSpace Here (HS _ value _) = value
  getHoldSpace (There pos) (HS str value tail) = getHoldSpace pos tail
  getHoldSpace (There pos) (LB str sc tail) = getHoldSpace pos tail

  getRoutineAux : {0 name : String}
                -> (sx : Variables)
                -> {st : ScriptType}
                -> (pos : (Label st, name) `Elem` sx)
                -> LinkedListStore sx io
                -> Exists (\sy => (getScriptByType st sy io, Thinning sy sx))
  getRoutineAux (sx :< (Label st, name))   Here (LB name sc store)
    = Evidence sx (sc, (id sx).Drop)
  getRoutineAux (sx :< (HoldSpace t, str)) (There pos) (HS str value store)
    = let Evidence sy (sc, tau) := getRoutineAux sx pos store
      in Evidence sy (sc, tau.Drop)
  getRoutineAux (sx :< (Label st, str))    (There pos) (LB str x store)
    = let Evidence sy (sc, tau) := getRoutineAux sx pos store
      in Evidence sy (sc, tau.Drop)

  getRoutine : {0 name : String}
            -> (sx : Variables)
            -> {st : ScriptType}
            -> (pos : (Label st, name) `Elem` sx)
            -> LinkedListStore sx io
            -> getScriptByType st sx io
  getRoutine sx pos store {st}
    = let Evidence sy (sc, tau) := getRoutineAux sx pos store
      in case st of
          Total => thin sc tau
          LineByLine => thin sc tau

  execOnHoldSpace : {0 name : String} -> {0 t : Type}
                  -> {0 xs : SnocList (VarType, String)}
                  -> (pos : (HoldSpace t, name) `Elem` xs)
                  -> LinkedListStore xs st
                  -> (t -> t)
                  -> LinkedListStore xs st
  execOnHoldSpace Here (HS name value hs) f = HS name (f value) hs
  execOnHoldSpace (There pos) (HS str value hs) f
    = HS str value (execOnHoldSpace pos hs f)
  execOnHoldSpace (There pos) (LB str name hs) f
    = LB str name (execOnHoldSpace pos hs f)

  dropIsTail : {tau : Thinning sx sy} -> IsTailThinning tau.Drop
            -> IsTailThinning tau
  dropIsTail {tau} IsId           = absurd tau
  dropIsTail      (IsDrop isTail) = isTail

  thin' : {0 sx,sy : Variables} -> LinkedListStore sy st -> (tau : Thinning sx sy)
        -> IsTailThinning tau -> LinkedListStore sx st
  thin' _ [<] _ = Empty
  thin' (HS name v store) tau.Keep IsId   = HS name v (thin' store tau IsId)
  thin' (LB name r store) tau.Keep IsId   = LB name r (thin' store tau IsId)
  thin' (HS name v store) tau.Drop isTail = thin' store tau (dropIsTail isTail)
  thin' (LB name r store) tau.Drop isTail = thin' store tau (dropIsTail isTail)

  thin : LinkedListStore sy st -> TailThinning sx sy -> LinkedListStore sx st
  thin store (tau ** isTail) = thin' store tau isTail

  public export
  VariableStore LinkedListStore where
    getHoldSpace = LinkedListStore.getHoldSpace
    getRoutine = LinkedListStore.getRoutine
    execOnHoldSpace = LinkedListStore.execOnHoldSpace
    empty = Empty
    thin = LinkedListStore.thin
    holdSpace = HS
    label = LB