module Sedris.VariableStore

import Sedris.Lang

public export
Variable : Type
Variable = (VarType, String)

public export
Variables : Type
Variables = SnocList Variable

data Weakening : Variables -> Variables -> Type where
  Weaken : (xs : List Variable) -> {auto 0 ford : sy = sx <>< xs}
    -> Weakening sx sy

data Thinning : Variables -> Variables -> Type where
  Lin : Thinning [<] sx
  (.Keep) : Thinning sx sy -> Thinning (sx :< y) (sy :< y)
  (.Drop) : Thinning sx sy -> Thinning  sx       (sy :< y)

-- Smart constructors
(:<) : Thinning sx sy -> (keep : Bool) ->
  Thinning (ifThenElse keep (sx :< y) sx) (sy :< y)
tau :< False = tau.Drop
tau :< True = tau.Keep

I,O : Bool
I = True
O = False

id : (sx : Variables) -> Thinning sx sx
id [<] = [<]
id (sx :< x) = (id sx).Keep

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

export
dropElem : (sx : Variables)
        -> (pos : x `Elem` sx)
        -> Thinning (dropElem sx pos) sx
dropElem (sx :< x) Here = (id sx).Drop
dropElem (sx :< x) (There pos) = (dropElem sx pos).Keep

dropLastAux : (ys : List Variable)
            -> Thinning sx sx'
            -> Thinning sx (sx' <>< ys)
dropLastAux [] tau = tau
dropLastAux (y :: ys) tau = dropLastAux ys tau.Drop

export
dropLast : (sx : Variables)
        -> (ys : List Variable)
        -> Thinning sx (sx <>< ys)
dropLast sx ys = dropLastAux ys (id sx)


-- id is neutral, (.) associative, i.e. a category whose objects are
-- Variables values and morphisms are thinnings

namespace Position
  public export
  thin : x `Elem` sx -> Thinning sx sy -> x `Elem` sy
  thin _ [<] impossible
  thin Here (tau.Keep) = Here
  thin (There pos) (tau.Keep) = There (pos `thin` tau)
  thin pos (tau .Drop) = There (pos `thin` tau)

namespace Cmd
  public export
  thin : Command sx zs st io -> Thinning sx sy -> Command sy zs st io
  -- thin (Replace x) y = Replace x
  -- thin (Exec f) y = Exec f
  -- thin Print y = ?thin_rhs_7
  -- thin (CreateHold holdSpace x) y = CreateHold holdSpace x
  -- thin (HoldApp holdSpace f {pos}) tau = HoldApp holdSpace f {pos = pos `thin` tau}
  -- thin (FromHold holdSpace f) y = ?thin_rhs_10
  -- thin (ExecOnHold holdSpace f) y = ?thin_rhs_11
  -- thin (Routine label x) y = ?thin_rhs_12
  -- thin (Call label) y = ?thin_rhs_13
  -- thin (IfThenElse f x z) y = ?thin_rhs_14
  -- thin (WithHoldContent holdSpace f) y = ?thin_rhs_15
  -- thin Quit y = ?thin_rhs_16

namespace ScriptCmd
  public export
  thin : ScriptCommand sx zs ts -> Thinning sx sy -> ScriptCommand sy zs ts
  thin (xs * x) y = ?thin_rhs_0
  thin (|*> x) y = ?thin_rhs_2
  thin (strs *> x) y = ?thin_rhs_3
  thin (|> x) y = ?thin_rhs_4

namespace Script
  public export
  thin : Script xs ts -> Thinning xs ys -> Script ys ts
  thin [] y = []
  thin (cmd :: cmds) y = ?thin_rhs_1

export
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
  thin : Store sy st -> Thinning sx sy -> Store sx st
  --- empty store
  empty : Store [<] st

namespace LinkedListStore
  export
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
          LineByLine => ?ncieow_1 --thin sc (dropLast sy zs)

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

  export
  VariableStore LinkedListStore where
    getHoldSpace = LinkedListStore.getHoldSpace
    getRoutine = LinkedListStore.getRoutine
    execOnHoldSpace = LinkedListStore.execOnHoldSpace
    empty = Empty
    thin = ?ncioerno
    holdSpace = HS
    label = LB

{-
  length : Store sx st -> Nat
  0 lengthPrf : {0 sx : Variables} -> (store : Store sx st)
              -> (length store = Prelude.SnocList.length sx)

  withOut : {0 xs : Variables} -> Store xs st -> (pos : x `Elem` xs)
          -> ( Store (Sedris.Lang.withOut xs pos) st
             , Store (Sedris.Lang.withOut xs pos) st -> Store xs st)
  empty : Store [<] st
  trim  : Store (vars <>< add) st -> (l : Nat)
        -> { auto 0 ford : l = Prelude.SnocList.length vars} -> Store vars st
  length : LinkedListStore sx st -> Nat
  length Empty = 0
  length (HS _ _ s) = S (length s)
  length (LB _ _ s) = S (length s)
  length (FL _ _ s) = S (length s)

  0 lengthPrf : (hs : LinkedListStore sx st) -> (length hs = length sx)
  lengthPrf Empty = Refl
  lengthPrf (HS _ _ s) = cong S (lengthPrf s)
  lengthPrf (LB _ _ s) = cong S (lengthPrf s)
  lengthPrf (FL _ _ s) = cong S (lengthPrf s)

  withOut : {0 xs : SnocList (VarType, String)}
            -> LinkedListStore xs st
            -> (pos : x `Elem` xs)
            ->  ( LinkedListStore (withOut xs pos) st
                , LinkedListStore (withOut xs pos) st -> LinkedListStore xs st)
  withOut Empty Here impossible
  withOut Empty (There pos) impossible
  withOut (HS name value store) Here = (store, (HS name value))
  withOut (HS name value store) (There pos)
    = let (store', f) := withOut store pos
      in  ( HS name value store'
          , (\case (HS name value store) => HS name value (f store)))
  withOut (LB name sc store) Here = (store, (LB name sc))
  withOut (LB name sc store) (There pos) = ?newkn
    -- = let (store', f) := withOut store pos
    --   in  ( LB name sc store'
    --       , (\case (LB name sc store) => LB name sc (f store)))
  withOut (FL name sc store) Here = (store, (FL name sc))
  withOut (FL name sc store) (There pos) = ?ncdjkn
    -- = let (store', f) := withOut store pos
    --   in  ( FL name sc store'
    --       , (\case (FL name sc store) => FL name sc (f store)))

  export
  VariableStore LinkedListStore where
    getHoldSpace = LinkedListStore.getHoldSpace
    getRoutine = LinkedListStore.getRoutine
    length = LinkedListStore.length
    lengthPrf = LinkedListStore.lengthPrf
    execOnHoldSpace = LinkedListStore.execOnHoldSpace
    withOut = LinkedListStore.withOut
    empty = Empty
    trim = ?ncioerno
    holdSpace = HS
    label = LB
    labelFileScript = FL
{-
trimHoldSpaces : {0 vars : SnocList (VarType, String)}
              -> {0 add : List (VarType, String)}
              -> {0 vars': SnocList (VarType, String)}
              -> {auto 0 ford' : vars <>< add = vars'}
              -> HoldSpacesState vars' st -> (l : Nat)
              -> { auto 0 ford : l = length vars}
              -> HoldSpacesState vars st
trimHoldSpaces hs 0 {ford} {st}
  = replace {p = (\x => HoldSpacesState x st)} ?nei Empty
trimHoldSpaces {vars} hs (S k) {ford = ford} {ford' = ford'}
  = let 0 nonEmpty := positiveLengthImpNonEmpty vars (sym ford)
    in ?bfeuiw

trim : VMState (vars <>< add) st
    -> (l : Nat)
    -> { auto 0 ford : l = length vars} -> VMState vars st
trim vm l {vars} {add} = lift (\hs => trimHoldSpaces {vars} {add} hs l) vm
-}
-}
