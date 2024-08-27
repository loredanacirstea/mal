import Lean.Data.RBMap
import Lean

set_option diagnostics true
set_option genSizeOfSpec false
set_option diagnostics.threshold 5000

universe u

inductive Vec (α : Type u) : Nat → Type u
| nil  : Vec α 0
| cons : α → Vec α n → Vec α (n + 1)
deriving Repr

-- Define the map function for Vec
def map {α : Type u} {β : Type v} {n : Nat} (f : α → β) : Vec α n → Vec β n
| Vec.nil          => Vec.nil
| Vec.cons x xs    => Vec.cons (f x) (map f xs)

-- Function to convert Vec to List
def toList {α : Type u} {n : Nat} : Vec α n → List α
| Vec.nil          => []
| Vec.cons x xs    => x :: toList xs

def listToVec  : (lst : List Types) → Vec Types lst.length
  | []      => Vec.nil
  | x :: xs => Vec.cons x (listToVec xs)

inductive KeyType
    | strKey : String → KeyType
    | keywordKey : String → KeyType
    deriving Repr

inductive Types : Type u
  | strVal (v : String)
  | intVal (v : Int)
  | floatVal (v : Float)
  | boolVal (v : Bool)
  | symbolVal (sym: String)
  | keywordVal (key: String)
  | listVal (el : List Types)
  | funcVal (el: Fun)
  | vecVal {n : Nat} (el : Vec Types n)
  | dictVal (el : Dict)
  | atomVal (el: Atom)
  | Nil
  -- deriving Repr

inductive Fun : Type u
  | builtin (name : String)
  | userDefined (env: Env) (params : Types) (body : Types)
  | macroFn (env: Env) (params : Types) (body : Types)

inductive Dict: Type u
  | empty : Dict
  | insert: KeyType → Types → Dict → Dict
  -- deriving Repr

structure Env where
  data : IO.Ref Dict
  outer : List (IO.Ref Dict)

inductive Atom
| v : Types -> Atom
| withmeta : Types → Types → Atom
-- deriving Repr


def defaultEnv : IO Env := do
  let ref ← IO.mkRef Dict.empty
  pure { data := ref, outer := [] }

instance : Inhabited Dict where
  default := Dict.empty

instance : Inhabited Types where
  default := Types.Nil

instance : Inhabited (List Types) where
  default := []

instance : Inhabited (Dict × Types) where
  default := (default, default)

def Dict.get : Dict → KeyType → Option Types
  | Dict.empty, _ => default
  | Dict.insert k v d, key =>
    match k, key with
    | KeyType.strKey ks, KeyType.strKey keyg => if ks = keyg then some v else d.get key
    | KeyType.keywordKey ks, KeyType.keywordKey keyg => if ks = keyg then some v else d.get key
    | KeyType.strKey ks, KeyType.keywordKey keyg => if ks = keyg then some v else d.get key
    | KeyType.keywordKey ks, KeyType.strKey keyg => if ks = keyg then some v else d.get key

def Dict.keys : Dict → List KeyType
  | Dict.empty => []
  | Dict.insert k _ d =>
    let restKeys := d.keys
    k :: restKeys

def Dict.values : Dict → List Types
  | Dict.empty => []
  | Dict.insert _ v d =>
    let restValues := d.values
    v :: restValues

def Dict.remove (d : Dict) (key : KeyType) : Dict :=
  match d with
  | Dict.empty => Dict.empty
  | Dict.insert k v rest =>
    match k, key with
      | KeyType.strKey ks, KeyType.strKey keyg => if ks = keyg then rest.remove key else Dict.insert k v (rest.remove key)
      | KeyType.keywordKey ks, KeyType.keywordKey keyg => if ks = keyg then rest.remove key else Dict.insert k v (rest.remove key)
      | KeyType.strKey ks, KeyType.keywordKey keyg => if ks = keyg then rest.remove key else Dict.insert k v (rest.remove key)
      | KeyType.keywordKey ks, KeyType.strKey keyg => if ks = keyg then rest.remove key else Dict.insert k v (rest.remove key)

def Dict.add : Dict → KeyType → Types → Dict
  | Dict.empty, key, value => Dict.insert key value Dict.empty
  | Dict.insert k v d, key, value =>
    match k, key with
      | KeyType.strKey ks, KeyType.strKey keyg => if ks = keyg then Dict.insert k value d else Dict.insert k v (d.add key value)
      | KeyType.keywordKey ks, KeyType.keywordKey keyg => if ks = keyg then Dict.insert k value d else Dict.insert k v (d.add key value)
      | KeyType.strKey ks, KeyType.keywordKey keyg => if ks = keyg then Dict.insert k value d else Dict.insert k v (d.add key value)
      | KeyType.keywordKey ks, KeyType.strKey keyg => if ks = keyg then Dict.insert k value d else Dict.insert k v (d.add key value)

-- Helper function to fold over all elements in a Dict
partial def Dict.fold (d : Dict) (init : α) (f : KeyType → Types → α → α) : α :=
  match d with
  | Dict.empty => init
  | Dict.insert k v d' => d'.fold (f k v init) f

-- -- Function to merge two Dicts
-- def Dict.merge (baseDict newDict : Dict) : Dict :=
--   let merged := newDict.fold baseDict (fun key v acc =>
--     match acc.get key with
--     | some (lBase, _) =>
--       if l > lBase then acc.add key l v else acc
--     | none => acc.add key l v)
--   merged

-- Function to extract the string from a Types.symbolVal
def getSymbol (t : Types) : Option String :=
  match t with
  | Types.symbolVal sym => some sym
  | _ => none

def getKeyword (t : Types) : Option String :=
  match t with
  | Types.keywordVal key => some key
  | _ => none

def buildDictWithSymbols (ref: Dict) (keys : List String) (values : List Types) : Dict :=
  match keys, values with
  | [], _ => Dict.empty
  | _, [] => Dict.empty
  | key :: keyTail, value :: valueTail =>
    let val := match value with
    | Types.symbolVal v =>
      let entry := ref.get (KeyType.strKey v)
      match entry with
      | some v => v
      | none => Types.Nil
    | _ => value
    let restDict := buildDictWithSymbols ref keyTail valueTail
    Dict.insert (KeyType.strKey key) val restDict

def buildDict (keys : List String) (values : List Types) : Dict :=
  match keys, values with
  | [], _ => Dict.empty
  | _, [] => Dict.empty
  | key :: keyTail, value :: valueTail =>
    let restDict := buildDict keyTail valueTail
    Dict.insert (KeyType.strKey key) value restDict

-- Get the current Dict from the Env
def Env.getDict (env: Env) : IO Dict := do
  env.data.get

-- Perform a key lookup in the current environment and its outer references
def Env.get (env: Env) (key: KeyType) : IO (Option Types) := do
  let data ← env.data.get
  match data.get key with
  | some value => pure (some value)
  | none =>
    -- If not found, iterate through the outer environments
    let rec searchInOuter (outers: List (IO.Ref Dict)) : IO (Option Types) :=
      match outers with
      | [] => pure none  -- No more environments to search
      | outerRef :: rest => do
        let outerDict ← outerRef.get
        match outerDict.get key with
        | some value => pure (some value)
        | none => searchInOuter rest  -- Continue searching in the next outer
    searchInOuter env.outer

def Env.getByStr (env: Env) (key: String) : IO (Option Types) := do
  env.get (KeyType.strKey key)

def Env.getByKeyword (env: Env) (key: String) : IO (Option Types) := do
  env.get (KeyType.keywordKey key)

def Env.keys (env: Env) : IO (List KeyType) := do
  return (← env.getDict).keys

def Env.values (env: Env) : IO (List Types) := do
  return (← env.getDict).values

-- def Env.remove (env: Env) (key: KeyType): Dict :=
--   env.data.remove key

def Env.add (env: Env) (key: KeyType) (value: Types): IO Env := do
  let dict := (← env.getDict).add key value
  env.data.set dict
  return env

def Env.new (outer: Env): IO Env := do
  let ref ← IO.mkRef Dict.empty
  pure { data := ref, outer := [outer.data] ++ outer.outer }

-- def Env.merge : Env → Env → Env
--   | Env.data _ d, e2 =>  Env.data e2.getLevel (d.merge e2.getDict)

-- def Env.mergeDict : Env → Dict → Env
--   | Env.data _ d, d2 =>  Env.data (d.merge d2)

def Types.toBool: Types -> Bool
  | Types.boolVal v => if v then true else false
  | Types.Nil => false
  | _ => true

def getFirst! (lst : List Types) : Types :=
  match lst with
  | []      => default
  | x :: _  => x

def escapeString (input : String) : String :=
  input.foldl (fun acc c =>
    acc ++ match c with
      | '\\' => "\\\\"
      -- | '"' => "\\\""
      | '\"' => "\\\""
      | '\n' => "\\n"
      | _ => String.singleton c
  ) ""

mutual
  partial def Types.toString (readably: Bool) (t:Types) : String :=
    match t with
    | Types.strVal v => stringToString readably v
    | Types.intVal v => s!"{v}"
    | Types.floatVal v => s!"{v}"
    | Types.boolVal v => s!"{v}"
    | Types.funcVal el => "#function" -- Fun.toString readably el
    | Types.listVal el => s!"({String.intercalate " " (el.map (Types.toString readably))})"
    | Types.dictVal el => "{" ++ s!"{Dict.toString readably el}" ++ "}"
    | Types.Nil => "nil"
    | Types.symbolVal sym => s!"{sym}"
    | Types.keywordVal key => s!":{key}"
    | Types.vecVal el =>
      let content := toList el
      s!"[{String.intercalate " " (content.map (Types.toString readably))}]"
    | Types.atomVal el => Atom.toString readably el

  partial def stringToString (readably: Bool) (v:String) : String :=
    if readably then s!"\"{escapeString v}\""
    else v

  partial def Atom.toString (readably: Bool) (t:Atom) : String :=
    match t with
    | Atom.v v => s!"(atom {v.toString readably})"
    | Atom.withmeta v _ => s!"(atom {v.toString readably})"

  partial def Fun.toString (readably: Bool) (t: Fun) : String :=
    match t with
    | Fun.userDefined _ params body => "(fn* " ++ s!"{(Types.toString readably params)}" ++ s!"{(Types.toString readably body)}" ++ ")"
    | Fun.macroFn _ params body => "(fn* " ++ s!"{(Types.toString readably params)}" ++ s!"{(Types.toString readably body)}" ++ ")"
    | Fun.builtin name => s!"{name}"

  partial def Dict.toString (readably: Bool) (d:Dict) : String :=
    match d with
    | Dict.empty => ""
    | Dict.insert key value Dict.empty =>
      match key with
      | KeyType.strKey k => s!"\"{k}\" {Types.toString readably value}"
      | KeyType.keywordKey k => s!":{k} {Types.toString readably value}"
    | Dict.insert key value rest =>
      let restStr := Dict.toString readably rest
      match key with
      | KeyType.strKey k => s!"{restStr} \"{k}\" {Types.toString readably value}"
      | KeyType.keywordKey k => s!"{restStr} :{k} {Types.toString readably value}"

  partial def Env.toString (readably: Bool) (e: Env) : IO String := do
    let dataDict ← e.data.get
    let dataStr := dataDict.toString readably

    -- Process each outer environment reference and build the outer string
    let outerStrs ← e.outer.mapM (fun v => do
      let outerDict ← v.get
      pure (outerDict.toString readably))

    -- Concatenate the outer strings
    let outerStr := String.intercalate ", " outerStrs

    -- Build the final string
    pure s!"<data: {dataStr} | outer: [{outerStr}]>"
end

def unwrapEnv (envRef : IO.Ref Env) : IO Env :=
  envRef.get

def wrapEnv (env: Env) : IO (IO.Ref Env) :=
  IO.mkRef env

def wrapEnvIO (ioEnv : IO Env) : IO (IO.Ref Env) := do
  let env ← ioEnv
  IO.mkRef env
