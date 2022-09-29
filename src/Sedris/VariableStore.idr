module Sedris.VariableStore

import Sedris.Lang

public export
Variables : Type
Variables = SnocList (VarType, String)

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

