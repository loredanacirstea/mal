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

mutual

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
    deriving Repr

  inductive Fun : Type u
    | builtin (name : String)
    | userDefined (env: Env) (params : Types) (body : Types)
    | macroFn (env: Env) (params : Types) (body : Types)

  inductive Dict: Type u
    | empty : Dict
    | insert: KeyType → Types → Dict → Dict
    deriving Repr

  inductive LevelDict: Type u
    | empty : LevelDict
    | insert: KeyType → Nat → Types → LevelDict → LevelDict
    deriving Repr

  inductive KLDict: Type u
    | empty : KLDict
    | insert: KeyType → Nat → KLDict → KLDict
    deriving Repr

  inductive Env: Type u
  | data: Nat → LevelDict → KLDict → Env

  inductive Atom
  | v : Types -> Atom
  | withmeta : Types → Types → Atom
  deriving Repr

end

instance : Inhabited Dict where
  default := Dict.empty

instance : Inhabited KLDict where
  default := KLDict.empty

instance : Inhabited LevelDict where
  default := LevelDict.empty

instance : Inhabited Types where
  default := Types.Nil

instance : Inhabited (List Types) where
  default := []

instance : Inhabited (Dict × Types) where
  default := (default, default)

instance : Inhabited Env where
  default := Env.data 0 LevelDict.empty KLDict.empty

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

def Dict.remove (d : Dict) (key : KeyType): Dict :=
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

def KLDict.get : KLDict → KeyType → Option Nat
  | KLDict.empty, _ => default
  | KLDict.insert k v d, key =>
    match k, key with
    | KeyType.strKey ks, KeyType.strKey keyg => if ks = keyg then some v else d.get key
    | KeyType.keywordKey ks, KeyType.keywordKey keyg => if ks = keyg then some v else d.get key
    | KeyType.strKey ks, KeyType.keywordKey keyg => if ks = keyg then some v else d.get key
    | KeyType.keywordKey ks, KeyType.strKey keyg => if ks = keyg then some v else d.get key

def KLDict.add : KLDict → KeyType → Nat → KLDict
  | KLDict.empty, key, value => KLDict.insert key value KLDict.empty
  | KLDict.insert k v d, key, value =>
    match k, key with
      | KeyType.strKey ks, KeyType.strKey keyg => if ks = keyg then KLDict.insert k value d else KLDict.insert k v (d.add key value)
      | KeyType.keywordKey ks, KeyType.keywordKey keyg => if ks = keyg then KLDict.insert k value d else KLDict.insert k v (d.add key value)
      | KeyType.strKey ks, KeyType.keywordKey keyg => if ks = keyg then KLDict.insert k value d else KLDict.insert k v (d.add key value)
      | KeyType.keywordKey ks, KeyType.strKey keyg => if ks = keyg then KLDict.insert k value d else KLDict.insert k v (d.add key value)

def LevelDict.get : LevelDict → KeyType → Nat → Option Types
  | LevelDict.empty, _, _ => default
  | LevelDict.insert k l v d, key, level =>
    match k, key with
    | KeyType.strKey ks, KeyType.strKey keyg => if ks = keyg && l = level then some v else d.get key level
    | KeyType.keywordKey ks, KeyType.keywordKey keyg => if ks = keyg && l = level then some v else d.get key level
    | KeyType.strKey ks, KeyType.keywordKey keyg => if ks = keyg && l = level then some v else d.get key level
    | KeyType.keywordKey ks, KeyType.strKey keyg => if ks = keyg && l = level then some v else d.get key level

def LevelDict.getRecursive (d : LevelDict) (key: KeyType) (level: Nat) : Option (Nat × Types) :=
  match d.get key level with
  | some v => (level, v)
  | none => if level > 0 then d.getRecursive key (level - 1) else none

def LevelDict.keys : LevelDict → List KeyType
  | LevelDict.empty => []
  | LevelDict.insert k _ _ d =>
    let restKeys := d.keys
    k :: restKeys

def LevelDict.values : LevelDict → List Types
  | LevelDict.empty => []
  | LevelDict.insert _ _ v d =>
    let restValues := d.values
    v :: restValues

def LevelDict.remove (d : LevelDict) (key : KeyType) (level: Nat) : LevelDict :=
  match d with
  | LevelDict.empty => LevelDict.empty
  | LevelDict.insert k l v rest =>
    match k, key with
      | KeyType.strKey ks, KeyType.strKey keyg => if ks = keyg && l = level then rest.remove key level else LevelDict.insert k l v (rest.remove key level)
      | KeyType.keywordKey ks, KeyType.keywordKey keyg => if ks = keyg && l = level then rest.remove key level else LevelDict.insert k l v (rest.remove key level)
      | KeyType.strKey ks, KeyType.keywordKey keyg => if ks = keyg && l = level then rest.remove key level else LevelDict.insert k l v (rest.remove key level)
      | KeyType.keywordKey ks, KeyType.strKey keyg => if ks = keyg && l = level then rest.remove key level else LevelDict.insert k l v (rest.remove key level)

def LevelDict.add : LevelDict → KeyType → Nat → Types → LevelDict
  | LevelDict.empty, key, level, value => LevelDict.insert key level value LevelDict.empty
  | LevelDict.insert k l v d, key, level, value =>
    match k, key with
      | KeyType.strKey ks, KeyType.strKey keyg => if ks = keyg && l = level then LevelDict.insert k level value d else LevelDict.insert k l v (d.add key level value)
      | KeyType.keywordKey ks, KeyType.keywordKey keyg => if ks = keyg && l = level then LevelDict.insert k level value d else LevelDict.insert k l v (d.add key level value)
      | KeyType.strKey ks, KeyType.keywordKey keyg => if ks = keyg && l = level then LevelDict.insert k level value d else LevelDict.insert k l v (d.add key level value)
      | KeyType.keywordKey ks, KeyType.strKey keyg => if ks = keyg && l = level then LevelDict.insert k level value d else LevelDict.insert k l v (d.add key level value)

-- Helper function to fold over all elements in a LevelDict and update the baseKeyLevelsDict
partial def LevelDict.fold (d : LevelDict) (acc : Env)
    (f : KeyType → Nat → Types → Env → Env) : Env :=
  match d with
  | LevelDict.empty => acc
  | LevelDict.insert k l v d' => d'.fold (f k l v acc) f

-- Function to extract the string from a Types.symbolVal
def getSymbol (t : Types) : Option String :=
  match t with
  | Types.symbolVal sym => some sym
  | _ => none

def getKeyword (t : Types) : Option String :=
  match t with
  | Types.keywordVal key => some key
  | _ => none

def Env.getLevel : Env → Nat
  | Env.data l _ _ => l

def Env.getDict : Env → LevelDict
  | Env.data _ d _ => d

def Env.getDictKeys : Env → KLDict
  | Env.data _ _ dk => dk

def Env.get : Env → KeyType → Nat → Option Types
  | Env.data _ d _, key => d.get key

def Env.getSelf : Env → KeyType → Option Types
  | Env.data l d _, key => d.get key l

def Env.getRecursive : Env → KeyType → Option (Nat × Types)
  | Env.data l d dk, key =>
    match dk.get key with
    | some l =>
      -- first try our cache of key => highest level
      match d.get key l with
      | some v => (l, v)
      | none => d.getRecursive key l
    | none => d.getRecursive key l

def Env.keys : Env → List KeyType
  | Env.data _ d _ => d.keys

def Env.values : Env → List KeyType
  | Env.data _ d _ => d.keys

def Env.add : Env → KeyType → Nat → Types → Env
  | Env.data l d dk, key, level, value =>
    let newdk := match dk.get key with
      | none => dk.add key level
      | some l => if l < level then dk.add key level else dk
    Env.data l (d.add key level value) newdk

def Env.increment : Env → Env
  | Env.data l d dk => Env.data (l + 1) d dk

def Env.merge (baseEnv : Env) (overwriteEnv : Env) : Env :=
  -- Use the fold function to merge overwriteDict into baseDict and update baseKeyLevelsDict accordingly.
  let overWriteMinLevel := overwriteEnv.getLevel
  let newenv := overwriteEnv.getDict.fold baseEnv (fun key l v acc =>
    match acc.getDict.get key l with
    | some _ =>
      -- Overwrite only if the level is greater than or equal to overWriteMinLevel.
      if l < overWriteMinLevel then acc
      else
        acc.add key l v
    | none =>  acc.add key l v
  )
  Env.data overwriteEnv.getLevel newenv.getDict newenv.getDictKeys

def Env.mergeDict (baseEnv : Env) (d2: LevelDict) (level2: Nat) (klDict: KLDict): Env :=
  baseEnv.merge (Env.data level2 d2 klDict)

def buildEnv (level: Nat) (keys : List String) (values : List Types) : Env :=
  match keys, values with
  | [], _ => Env.data level LevelDict.empty KLDict.empty
  | _, [] =>  Env.data level LevelDict.empty KLDict.empty
  | key :: keyTail, value :: valueTail =>
    let restEnv := buildEnv level keyTail valueTail
    restEnv.add (KeyType.strKey key) level value

def buildEnv2 (env: Env) (keys : List String) (values : List Types) : Env :=
  match keys, values with
  | [], _ => Env.data env.getLevel LevelDict.empty KLDict.empty
  | _, [] =>  Env.data env.getLevel LevelDict.empty KLDict.empty
  | key :: keyTail, value :: valueTail =>
    let val := match value with
    | Types.symbolVal v =>
      let entry := env.getRecursive (KeyType.strKey v)
      match entry with
      | some (_, v) => v
      | none => Types.Nil
    | _ => value
    let restEnv := buildEnv2 env keyTail valueTail
    restEnv.add (KeyType.strKey key) env.getLevel val

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
    | Types.funcVal el => Fun.toString readably el
    -- | Types.funcVal v => "(" ++ s!"{(Types.toString v)}" ++ ")"
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

  partial def Fun.toString (readably: Bool) (t:Fun) : String :=
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

  partial def KLDict.toString (readably: Bool) (d:KLDict) : String :=
    match d with
    | KLDict.empty => ""
    | KLDict.insert key value KLDict.empty =>
      match key with
      | KeyType.strKey k => s!"\"{k}\" {value}"
      | KeyType.keywordKey k => s!":{k} {value}"
    | KLDict.insert key value rest =>
      let restStr := KLDict.toString readably rest
      match key with
      | KeyType.strKey k => s!"{restStr} \"{k}\" {value}"
      | KeyType.keywordKey k => s!"{restStr} :{k} {value}"

  partial def LevelDict.toString (readably: Bool) (d:LevelDict) : String :=
    match d with
    | LevelDict.empty => ""
    | LevelDict.insert key l value LevelDict.empty =>
      match key with
      | KeyType.strKey k => s!"\"{k}\" ({l}) {Types.toString readably value}"
      | KeyType.keywordKey k => s!":{k} ({l}) {Types.toString readably value}"
    | LevelDict.insert key l value rest =>
      let restStr := LevelDict.toString readably rest
      match key with
      | KeyType.strKey k => s!"{restStr} \"{k}\" ({l}) {Types.toString readably value}"
      | KeyType.keywordKey k => s!"{restStr} :{k} ({l}) {Types.toString readably value}"

  partial def Env.toString (readably: Bool) (e:Env) : String :=
  match e with
  | Env.data l d dk => s!"level: {l} dict: {d.toString readably} dictkeys: {dk.toString readably}"
end
