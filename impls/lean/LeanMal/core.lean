import Lean
import Mathlib
import LeanMal.types

universe u

def sum (ref : Dict := Dict.empty) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  match lst with
  | []                                   => Except.ok (ref, Types.intVal 0)
  | [Types.intVal x]                     => Except.ok (ref, Types.intVal x)
  | [Types.intVal x, Types.intVal y]     => Except.ok (ref, Types.intVal (x + y))
  | [Types.floatVal x]                   => Except.ok (ref, Types.floatVal x)
  | [Types.floatVal x, Types.floatVal y] => Except.ok (ref, Types.floatVal (x + y))
  | _                                    => Except.error (ref, "+ operator not supported")

def sub (ref : Dict := Dict.empty) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  match lst with
  | []                                   => Except.ok (ref, Types.intVal 0)
  | [Types.intVal x]                     => Except.ok (ref, Types.intVal x)
  | [Types.intVal x, Types.intVal y]     => Except.ok (ref, Types.intVal (x - y))
  | [Types.floatVal x]                   => Except.ok (ref, Types.floatVal x)
  | [Types.floatVal x, Types.floatVal y] => Except.ok (ref, Types.floatVal (x - y))
  | _                                    => Except.error (ref, "- operator not supported")

def mul (ref : Dict := Dict.empty) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  match lst with
  | []                                   => Except.ok (ref, Types.intVal 0)
  | [Types.intVal x]                     => Except.ok (ref, Types.intVal x)
  | [Types.intVal x, Types.intVal y]     => Except.ok (ref, Types.intVal (x * y))
  | [Types.floatVal x]                   => Except.ok (ref, Types.floatVal x)
  | [Types.floatVal x, Types.floatVal y] => Except.ok (ref, Types.floatVal (x * y))
  | _                                    => Except.error (ref, "* operator not supported")

def div (ref : Dict := Dict.empty) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  match lst with
  | []                                   => Except.ok (ref, Types.intVal 0)
  | [Types.intVal x]                     => Except.ok (ref, Types.intVal x)
  | [Types.intVal x, Types.intVal y]     => Except.ok (ref, Types.intVal (x / y))
  | [Types.floatVal x]                   => Except.ok (ref, Types.floatVal x)
  | [Types.floatVal x, Types.floatVal y] => Except.ok (ref, Types.floatVal (x / y))
  | _                                    => Except.error (ref, "/ operator not supported")

def ltInternal (first: Types) (second: Types) (orEq: Bool) : Bool :=
  match first, second with
  | Types.intVal n, Types.intVal v => n < v || (if orEq then n == v else false)
  | Types.intVal n, Types.floatVal v => (Float.ofInt n) < v || (if orEq then (Float.ofInt n) == v else false)
  | Types.floatVal n, Types.floatVal v => n < v || (if orEq then n == v else false)
  | Types.floatVal n, Types.intVal v => n < (Float.ofInt v) || (if orEq then n == (Float.ofInt v) else false)
  | Types.strVal n, Types.strVal v => n < v || (if orEq then n == v else false)
  | _, _ => false

def lt (ref: Dict) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  if lst.length < 2 then Except.error (ref, "eq: 2 arguments required")
  else
    let first := lst[0]!
    let second := lst[1]!
    let res := ltInternal first second false
    Except.ok (ref, Types.boolVal res)

def lte (ref: Dict) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  if lst.length < 2 then Except.error (ref, "eq: 2 arguments required")
  else
    let first := lst[0]!
    let second := lst[1]!
    let res := ltInternal first second true
    Except.ok (ref, Types.boolVal res)

def gtInternal (first: Types) (second: Types) (orEq: Bool) : Bool :=
  match first, second with
  | Types.intVal n, Types.intVal v => n > v || (if orEq then n == v else false)
  | Types.intVal n, Types.floatVal v => (Float.ofInt n) > v || (if orEq then (Float.ofInt n) == v else false)
  | Types.floatVal n, Types.floatVal v => n > v || (if orEq then n == v else false)
  | Types.floatVal n, Types.intVal v => n > (Float.ofInt v) || (if orEq then n == (Float.ofInt v) else false)
  | Types.strVal n, Types.strVal v => n > v || (if orEq then n == v else false)
  | _, _ => false

def gt (ref: Dict) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  if lst.length < 2 then Except.error (ref, "eq: 2 arguments required")
  else
    let first := lst[0]!
    let second := lst[1]!
    let res := gtInternal first second false
    Except.ok (ref, Types.boolVal res)

def gte (ref: Dict) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  if lst.length < 2 then Except.error (ref, "eq: 2 arguments required")
  else
    let first := lst[0]!
    let second := lst[1]!
    let res := gtInternal first second true
    Except.ok (ref, Types.boolVal res)

mutual
  partial def eqList (n: List Types) (v: List Types) (strict: Bool) : Bool :=
    match n, v with
    | [], [] => true
    | [], _ => false
    | _, [] => false
    | a :: nrest, b :: vrest =>
      if !(eqInternal a b strict) then false
      else eqList nrest vrest strict

  -- partial def eqDictKeys (k1: List KeyType) (k2: List KeyType) : Bool :=
  --   match k1, k2 with
  --   | KeyType.strKey x,

  partial def eqDict (n: Dict) (v: Dict) (strict: Bool) : Bool :=
    match n, v with
    | Dict.empty, Dict.empty => true
    | d1, d2 =>
      let keys1 := getKeys d1
      let keys2 := getKeys d2
      if keys1.length != keys2.length then false
      else
        keys1.all (fun k =>
          match (getEntry d1 k, getEntry d2 k) with
          | (some v1, some v2) => eqInternal v1 v2 strict
          | _ => false)

  partial def eqInternal (first: Types) (second: Types) (strict: Bool) : Bool :=
    match first, second with
    | Types.intVal n, Types.intVal v => n == v
    | Types.intVal n, Types.floatVal v => if strict then false else (Float.ofInt n) == v
    | Types.floatVal n, Types.floatVal v => n == v
    | Types.floatVal n, Types.intVal v => if strict then false else n == (Float.ofInt v)
    | Types.strVal n, Types.strVal v => n == v
    | Types.boolVal n, Types.boolVal v => n == v
    | Types.symbolVal n, Types.symbolVal v => n == v
    | Types.keywordVal n, Types.keywordVal v => n == v
    | Types.Nil, Types.Nil => true
    | Types.listVal n, Types.listVal v =>
      if n.length != v.length then false
      else eqList n v strict
    | Types.vecVal nvec, Types.vecVal vvec =>
      let n := toList nvec
      let v := toList vvec
      if n.length != v.length then false
      else eqList n v strict
    | Types.dictVal n, Types.dictVal v => eqDict n v strict
    | _, _ => false

end

def eq (ref: Dict) (lst: List Types) (strict: Bool) : Except (Dict × String) (Dict × Types) :=
  if lst.length < 2 then Except.error (ref, "eq: 2 arguments required")
  else
    let first := lst[0]!
    let second := lst[1]!
    let res := eqInternal first second strict
    Except.ok (ref, Types.boolVal res)

def prStrInternal (lst: List Types) (printReadably: Bool) (sep: String) : String :=
  let elems := lst.map (fun x => x.toString printReadably)
  String.intercalate sep elems

def KEY_LOGS_INFO := "LOGS_INFO"
def KEY_LOGS_DEBUG := "LOGS_DEBUG"
def KEY_DEBUG_EVAL := "DEBUG-EVAL"

def getLogs (ref: Dict) (type: String): List Types :=
  match getEntry ref (KeyType.strKey type) with
    | some v => match v with
      | Types.listVal loglist => loglist
      | _ => []
    | _ => []

def getDebugEval (ref: Dict): Bool :=
  match getEntry ref (KeyType.strKey KEY_DEBUG_EVAL) with
    | some v => match v with
      | Types.boolVal v => v
      | Types.Nil => false
      | _ => false
    | _ => false

def getLogsInfo (ref: Dict): List Types :=
  getLogs ref KEY_LOGS_INFO

def logInfo (ref: Dict) (msg: String): Dict :=
  let loglist := getLogs ref KEY_LOGS_INFO
  let newlogs := loglist ++ [(Types.strVal msg)]
  ref.insert (KeyType.strKey KEY_LOGS_INFO) (Types.listVal newlogs)

def prStrFunc (ref: Dict) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  let str := prStrInternal lst true " "
  Except.ok (ref, Types.strVal str)

def prnFunc (ref: Dict) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  let str := prStrInternal lst true " "
  let newRef := logInfo ref str
  Except.ok (newRef, Types.Nil)

def printlnFunc (ref: Dict) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  let str := prStrInternal lst false " "
  let newRef := logInfo ref str
  Except.ok (newRef, Types.Nil)

def strFunc (ref: Dict) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  let str := prStrInternal lst false ""
  Except.ok (ref, Types.strVal str)

def countFunc(ref: Dict) (lst: List Types) : Except (Dict × String) (Dict × Types) :=
  if lst.length < 1 then Except.error (ref, "count: 1 argument required")
  else
    let x := lst[0]!
    match x with
      | Types.listVal v => Except.ok (ref, Types.intVal v.length)
      | Types.Nil => Except.ok (ref, Types.intVal 0)
      | _ => Except.error (ref, "count called on non-sequence")

def evalFnNative (ref : Dict := Dict.empty) (name: String) (results: List Types): Except (Dict × String) (Dict × Types) :=
    match name with
    | "+" => sum ref results
    | "-" => sub ref results
    | "*" => mul ref results
    | "/" => div ref results
    | "<" => lt ref results
    | "<=" => lte ref results
    | ">" => gt ref results
    | ">=" => gte ref results
    | "=" => eq ref results false
    | "prn" => prnFunc ref results
    | "pr-str" => prStrFunc ref results
    | "str" => strFunc ref results
    | "println" => printlnFunc ref results
    | "list" => Except.ok (ref, Types.listVal results)
    | "count" => countFunc ref results
    | _ => match results with
        | [x] => match x with
          | Types.listVal x => match name with
            | "list?" => Except.ok (ref, Types.boolVal true)
            | "empty?" => Except.ok (ref, Types.boolVal (x.length == 0))
            | _ => Except.ok (ref, Types.boolVal false)
          | _   => Except.ok (ref, Types.boolVal false)
        | _   => Except.error (ref, s!"'{name}' not found")

def loadFnNative (ref: Dict) (name: String) : Dict :=
  ref.insert (KeyType.strKey name) (Types.funcVal (Fun.builtin name))

def loadFnNativeFold (ref: Dict) (fnNames : List String) : Dict :=
  fnNames.foldl loadFnNative ref

def coreFnSymbols: List String := [
  "+", "-", "*", "/",
  "<", "<=", ">", ">=", "=",
  "list", "list?", "empty?", "count",
  "prn", "pr-str", "str", "println",
]

def loadFnNativeAll (ref: Dict) : Dict :=
  let newRef := loadFnNativeFold ref coreFnSymbols
  ((
    newRef.insert (KeyType.strKey KEY_LOGS_INFO) (Types.listVal [])
  ).insert (KeyType.strKey KEY_LOGS_DEBUG) (Types.listVal [])
  ).insert (KeyType.strKey KEY_DEBUG_EVAL) (Types.boolVal false)
