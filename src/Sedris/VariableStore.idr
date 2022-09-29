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

-- id is neutral, (.) associative, i.e. a category whose objects are
-- Variables values and morphisms are thinnings


Ex1, Ex2 : Thinning [<(Label, "x")] [< (Label, "x"), (Label, "y"), (Label, "x")]
Ex1 = [< I, O, O]
Ex2 = [< O, O, I]

namespace Position
  public export
  thin : x `Elem` sx -> Thinning sx sy -> x `Elem` sy
  thin _ [<] impossible
  thin Here (tau.Keep) = Here
  thin (There pos) (tau.Keep) = There (pos `thin` tau)
  thin pos (tau .Drop) = There (pos `thin` tau)

namespace Cmd
  public export
  thin : Command sx zs ts -> Thinning sx sy -> Command sy zs ts
  thin (Replace x) y = Replace x
  thin (Exec f) y = Exec f
  thin Print y = ?thin_rhs_7
  thin (CreateHold holdSpace x) y = CreateHold holdSpace x
  thin (HoldApp holdSpace f {pos}) tau = HoldApp holdSpace f {pos = pos `thin` tau}
  thin (FromHold holdSpace f) y = ?thin_rhs_10
  thin (ExecOnHold holdSpace f) y = ?thin_rhs_11
  thin (Routine label x) y = ?thin_rhs_12
  thin (Call label) y = ?thin_rhs_13
  thin (IfThenElse f x z) y = ?thin_rhs_14
  thin (WithHoldContent holdSpace f) y = ?thin_rhs_15
  thin Quit y = ?thin_rhs_16

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

namespace FakeStore
  data FakeStore : Variables -> Type where
    Nil : FakeStore [<]
    (:<) : FakeStore sx -> Unit -> FakeStore (sx :< x)

  thin : FakeStore sy -> Thinning sx sy -> FakeStore sx
  thin x y = ?thin_rhs

{-
export
interface VariableStore (Store : Variables -> FileScriptType -> Type) where
  getHoldSpace : {0 name : String} -> {0 t : Type} -> {0 sx : Variables}
              -> (pos : (HoldSpace t, name) `Elem` sx)
              -> Store sx st -> t
  getRoutine : {0 name : String} -> {0 sx : Variables}
            -> (pos : (Label, name) `Elem` sx)
            -> Store sx st
            -> Exists (\ys => ( Script ys st
                              , Store ys st
                              , Store ys st -> Store sx st))
  length : Store sx st -> Nat
  0 lengthPrf : {0 sx : Variables} -> (store : Store sx st)
              -> (length store = Prelude.SnocList.length sx)
  execOnHoldSpace : {0 name : String} -> {0 t : Type}
                  -> {0 sx : Variables} -> (pos : (HoldSpace t, name) `Elem` sx)
                  -> Store sx st -> (t -> t)
                  -> Store sx st
  withOut : {0 xs : Variables} -> Store xs st -> (pos : x `Elem` xs)
          -> ( Store (Sedris.Lang.withOut xs pos) st
             , Store (Sedris.Lang.withOut xs pos) st -> Store xs st)
  empty : Store [<] st
  trim  : Store (vars <>< add) st -> (l : Nat)
        -> { auto 0 ford : l = Prelude.SnocList.length vars} -> Store vars st
  holdSpace : (name : String) -> {t : Type} -> (value : t) -> Store sx st
            -> Store (sx :< (HoldSpace t, name)) st
  label : (name : String) -> (Script sx st) -> Store sx st
        -> Store (sx :< (Label, name)) st
  labelFileScript : (name : String) -> (FileScript sx st) -> Store sx st
                  -> Store (sx :< (LabelFileScript, name)) st

namespace LinkedListStore
  export
  data LinkedListStore : Variables -> FileScriptType -> Type where
    Empty : LinkedListStore [<] st
    HS : (name : String) -> {t : Type} -> (value : t) -> LinkedListStore sx st
      -> LinkedListStore (sx :< (HoldSpace t, name)) st
    LB : (name : String) -> (Script sx st) -> LinkedListStore sx st
      -> LinkedListStore (sx :< (Label, name)) st
    FL : (name : String) -> (FileScript sx st) -> LinkedListStore sx st
      -> LinkedListStore (sx :< (LabelFileScript, name)) st

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

  getHoldSpace : {0 name : String} -> {0 t : Type}
              -> {0 xs : SnocList (VarType, String)}
              -> (pos : (HoldSpace t, name) `Elem` xs)
              -> LinkedListStore xs st
              -> t
  getHoldSpace Here (HS _ value _) = value
  getHoldSpace (There pos) (HS str value tail) = getHoldSpace pos tail
  getHoldSpace (There pos) (LB str sc tail) = getHoldSpace pos tail
  getHoldSpace (There pos) (FL str sc tail) = getHoldSpace pos tail

  getRoutine : {0 name : String} -> {0 xs : SnocList (VarType, String)}
            -> (pos : (Label, name) `Elem` xs)
            -> LinkedListStore xs st
            -> Exists (\ys => (Script ys st
                              , LinkedListStore ys st
                              , (LinkedListStore ys st -> LinkedListStore xs st)))
  getRoutine Here (LB name sc hs {sx}) = Evidence sx (sc, hs, (LB name sc))
  getRoutine (There pos) (HS str value hs)
    = let Evidence sx (sc, hs', f) := getRoutine pos hs
      in Evidence sx (sc, hs', (\hs => HS str value (f hs)))
  getRoutine (There pos) (LB str name hs)
    = let Evidence sx (sc, hs', f) := getRoutine pos hs
      in Evidence sx (sc, hs', (\hs => LB str name (f hs)))
  getRoutine (There pos) (FL str name hs)
    = let Evidence sx (sc, hs', f) := getRoutine pos hs
      in Evidence sx (sc, hs', (\hs => FL str name (f hs)))

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
  execOnHoldSpace (There pos) (FL str name hs) f
    = FL str name (execOnHoldSpace pos hs f)

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
