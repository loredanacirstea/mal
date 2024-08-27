import LeanMal.reader
import LeanMal.printer

universe u

def READ (input : String): Except String Types :=
  read_str.{u} input

def sum (env: IO.Ref Env) (lst: List Types) : IO (IO.Ref Env × Types) := do
  match lst with
  | []                                   => return (env, Types.intVal 0)
  | [Types.intVal x]                     => return (env, Types.intVal x)
  | [Types.intVal x, Types.intVal y]     => return (env, Types.intVal (x + y))
  | [Types.floatVal x]                   => return (env, Types.floatVal x)
  | [Types.floatVal x, Types.floatVal y] => return (env, Types.floatVal (x + y))
  | _                                    => throw (IO.userError "+ operator not supported")

def sub (env: IO.Ref Env) (lst: List Types) : IO (IO.Ref Env × Types) := do
  match lst with
  | []                                   => return (env, Types.intVal 0)
  | [Types.intVal x]                     => return (env, Types.intVal x)
  | [Types.intVal x, Types.intVal y]     => return (env, Types.intVal (x - y))
  | [Types.floatVal x]                   => return (env, Types.floatVal x)
  | [Types.floatVal x, Types.floatVal y] => return (env, Types.floatVal (x - y))
  | _                                    => throw (IO.userError "- operator not supported")

def mul (env: IO.Ref Env) (lst: List Types) : IO (IO.Ref Env × Types) := do
  match lst with
  | []                                   => return (env, Types.intVal 0)
  | [Types.intVal x]                     => return (env, Types.intVal x)
  | [Types.intVal x, Types.intVal y]     => return (env, Types.intVal (x * y))
  | [Types.floatVal x]                   => return (env, Types.floatVal x)
  | [Types.floatVal x, Types.floatVal y] => return (env, Types.floatVal (x * y))
  | _                                    => throw (IO.userError "* operator not supported")

def div (env: IO.Ref Env) (lst: List Types) : IO (IO.Ref Env × Types) := do
  match lst with
  | []                                   => return (env, Types.intVal 0)
  | [Types.intVal x]                     => return (env, Types.intVal x)
  | [Types.intVal x, Types.intVal y]     => return (env, Types.intVal (x / y))
  | [Types.floatVal x]                   => return (env, Types.floatVal x)
  | [Types.floatVal x, Types.floatVal y] => return (env, Types.floatVal (x / y))
  | _                                    => throw (IO.userError "/ operator not supported")

def evalFnNative (env: IO.Ref Env) (name: String) (results: List Types): IO (IO.Ref Env × Types) := do
    match name with
    | "+" => sum env results
    | "-" => sub env results
    | "*" => mul env results
    | "/" => div env results
    | _   => throw (IO.userError s!"'{name}' not found")

mutual

  partial def evalTypes (env: IO.Ref Env) (ast : Types) : IO (IO.Ref Env × Types) := do
    match ast with
    | Types.symbolVal v   =>
      match (← unwrapEnv env).getByStr v with
      | some (_, vi) => return (env, vi)
      | none    => return (env, Types.symbolVal v )
    | Types.listVal el    => (evalList env el)
    | Types.vecVal el     => (evalVec env (toList el))
    | Types.dictVal el    => (evalDict env el)
    | x                   => return (env, x)

  partial def evalFunc (env: IO.Ref Env) (head : Types) (args : List Types) : IO (IO.Ref Env × Types) := do
    let (env2, fn) ← evalTypes env head
    evalFuncVal env2 fn args

  partial def evalFuncVal (env: IO.Ref Env) (fn: Types) (args: List Types) : IO (IO.Ref Env × Types) := do
    -- first execute each function argument - reduce computation
    let (newEnv, results) ← evalFuncArgs env args
    match fn with
      | Types.symbolVal name => evalFnNative newEnv name results
      | Types.funcVal v      => match v with
        | Fun.builtin name => evalFnNative newEnv name results
        | Fun.userDefined fenv params body =>
          let keys: List String := match params with
            | Types.listVal v => v.map fun x => x.toString false
            | _               => []
          let argsDict := (buildDict 0 keys results)
          let merged := ((← unwrapEnv newEnv).merge fenv).mergeDict (fenv.getLevel + 1) argsDict
          evalTypes (← wrapEnv merged) body
        | Fun.macroFn _ _ _ => throw (IO.userError "macro not implemented")
      | _ => throw (IO.userError s!"`unexpected token, expected: function`")

  partial def evalList (env: IO.Ref Env) (lst : List Types) : IO (IO.Ref Env × Types) := do
    if List.length lst == 0 then return (env, Types.listVal lst)
    else
      let head := lst[0]!
      match lst[0]! with
      | Types.symbolVal v => match v with
        | _ => evalFunc env head (lst.drop 1)
      | _ => evalFunc env head (lst.drop 1)

  partial def evalVec (env: IO.Ref Env) (elems : List Types) : IO (IO.Ref Env × Types) := do
    let (newEnv, results) ← evalFuncArgs env elems
    return (newEnv, Types.vecVal (listToVec results))

  partial def evalDict (env: IO.Ref Env) (lst : Dict) : IO (IO.Ref Env × Types) := do
    let (newEnv, newDict) ← evalDictInner env lst
    return (newEnv, Types.dictVal newDict)

  partial def evalDictInner (env: IO.Ref Env) (lst : Dict) : IO (IO.Ref Env × Dict) := do
    match lst with
      | Dict.empty => return (env, lst)
      | Dict.insert k _ v restDict =>
        let (newEnv, newVal) ← evalTypes env v
        let (updatedEnv, updatedDict) ← evalDictInner newEnv restDict
        let newDict := Dict.insert k 0 newVal updatedDict
        return (updatedEnv, newDict)

  partial def evalFuncArgs (env: IO.Ref Env) (args: List Types) : IO (IO.Ref Env × List Types) := do
  args.foldlM (fun (res : IO.Ref Env × List Types) (x : Types) => do
    let (r, acc) := res
    let (updatedenv, res) ← evalTypes r x
    return (updatedenv, acc ++ [res])
  ) (env, [])
end

def PRINT (ast : Types): String :=
  pr_str true ast

def rep (input : String): IO String := do
  match READ.{u} input with
  | Except.ok result =>
    try
      let (_, res) ← evalTypes (← wrapEnv (Env.data 0 Dict.empty)) result
      return PRINT res
    catch
      | e => return s!"Error: {e}"
  | Except.error err =>
    return s!"Parsing failed: {err}"

def main : IO Unit := do
  let mut donext := true
  while donext do
    IO.print "user> "
    let stdin ← IO.getStdin
    let input ← stdin.getLine
    let value := input.trim
    if value = "exit" then
      donext := false
      IO.println "Exiting REPL."
    if value.isEmpty then
      donext := false
    else
      let output ← rep.{u} value
      IO.println output
