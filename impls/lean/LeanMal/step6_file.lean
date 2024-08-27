import LeanMal.reader
import LeanMal.printer
import LeanMal.core

universe u

def makeFn (env: IO.Ref Env) (args : List Types) : IO (IO.Ref Env × Types) := do
  if args.length < 2 then throw (IO.userError "unexpected syntax")
  else
    let p := args[0]!
    let body := args[1]!
    let params := match p with
      | Types.vecVal x => Types.listVal (toList x)
      | _ => p
    let newfn := Fun.userDefined (← unwrapEnv env).increment params body
    return (env, Types.funcVal newfn)

def splitOnAmpersand (input : List String) : (List String × List String) :=
  let rec loop (acc1 : List String) (rest : List String) : (List String × List String) :=
    match rest with
    | []         => (acc1, [])  -- If no "&" found, second list is empty
    | "&" :: xs  => match xs with
      | [] => (acc1, [])  -- If "&" is the last element, second list is empty
      | y :: _ => (acc1, [y])  -- Add the next element after "&" to the second list
    | x :: xs    => loop (acc1 ++ [x]) xs  -- Accumulate elements before "&"
  loop [] input

mutual
   partial def evalTypes (env: IO.Ref Env) (ast : Types) : IO (IO.Ref Env × Types) := do
    if ← getDebugEval env then IO.println s!"EVAL:{pr_str true ast}"
    match ast with
    | Types.symbolVal v   => match (← unwrapEnv env).getByStr v with
      | some (_, vi) => return (env, vi)
      | none => throw (IO.userError s!"'{v}' not found")
    | Types.listVal el    => (evalList env el)
    | Types.vecVal el     => (evalVec env (toList el))
    | Types.dictVal el    => (evalDict env el)
    | x                   => return (env, x)

  partial def evalFunc (env: IO.Ref Env) (head : Types) (args : List Types) : IO (IO.Ref Env × Types) := do
    let (env2, fn) ← evalTypes env head
    let (fenv, res) ← evalFuncVal env2 fn args
    -- after executing a function, propagate atoms (defined in outer environments) to the parent scope
    return ((forwardMutatedAtoms fenv env), res) -- TODO
    return (env, res)

  partial def evalFuncVal (env: IO.Ref Env) (fn: Types) (args: List Types) : IO (IO.Ref Env × Types) := do
    -- first execute each function argument - reduce computation
    let (newEnvIO, results) ← evalFuncArgs env args
    let newEnv ← unwrapEnv newEnvIO
    match fn with
      | Types.funcVal v      => match v with
        | Fun.builtin name => evalFnNative newEnvIO name results args
        | Fun.userDefined fref params body =>
          let allkeys: List String := match params with
            | Types.listVal v => v.map fun x => x.toString false
            | _               => []
          let (keys, variadic) := splitOnAmpersand allkeys
          let normalArgs := results.take keys.length
          let variadicArg := results.drop keys.length
          let argVals := normalArgs ++ [Types.listVal variadicArg]
          let argsLevel := if fref.getLevel >= newEnv.getLevel then fref.getLevel + 1 else newEnv.getLevel + 1

          let argsDict := (buildDict argsLevel (keys ++ variadic) argVals)
          let merged := (newEnv.merge fref).mergeDict argsLevel argsDict

          evalTypes (← wrapEnv merged) body
        | Fun.macroFn _ _ _ => throw (IO.userError "macro not implemented")
      | _ => throw (IO.userError s!"`unexpected token, expected: function`")

  partial def evalList (env: IO.Ref Env) (lst : List Types) : IO (IO.Ref Env × Types) := do
    if List.length lst == 0 then return (env, Types.listVal lst)
    else
      let head := lst[0]!
      match lst[0]! with
      | Types.symbolVal v => match v with
        | "def!" => evalDefn env (lst.drop 1)
        | "let*" => evalLet env (lst.drop 1)
        | "do" => evalDo env (lst.drop 1)
        | "if" => evalIf env (lst.drop 1)
        | "fn*" => makeFn env (lst.drop 1)
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

  partial def evalFuncArgs (env: IO.Ref Env) (args: List Types) : IO (IO.Ref Env × List Types) :=
    args.foldlM (fun (res : IO.Ref Env × List Types) (x : Types) => do
      let (r, acc) := res
      let (updatedenv, res) ← evalTypes r x
      return (updatedenv, acc ++ [res])
    ) (env, [])

  partial def evalDefn (envr: IO.Ref Env) (args : List Types) : IO (IO.Ref Env × Types) := do
    if args.length < 2 then throw (IO.userError "def! unexpected syntax")
    else
      let key := args[0]!
      let body := args[1]!
      let env ← unwrapEnv envr
      let (newEnvR, value) ← (evalTypes envr body)
      let newEnv ← unwrapEnv newEnvR

      match key with
        | Types.symbolVal v =>
          let refResult := newEnv.add (KeyType.strKey v) env.getLevel value
          return (← wrapEnv refResult, value)
        | _ => throw (IO.userError s!"def! unexpected token, expected: symbol")

  partial def evalLet (envr: IO.Ref Env) (args : List Types) : IO (IO.Ref Env × Types) := do
    if args.length < 2 then throw (IO.userError "let*: unexpected syntax")
    else
      let pairs := args[0]!
      let body := args[1]!
      let env ← unwrapEnv envr
      let newEnv ← match pairs with
      | Types.listVal v => evalLetArgs (← wrapEnv env.increment) v
      | Types.vecVal v => evalLetArgs (← wrapEnv env.increment) (toList v)
      | _ => throw (IO.userError s!"unexpected token type: ${pairs.toString true}, expected: list or vector")

      let (letref, result) ← evalTypes newEnv body
      -- after executing let*, propagate atoms (defined in outer environments) and logs to the parent scope
      -- return ((forwardMutatedAtoms letref env), result) -- TODO
      return (← wrapEnv env, result)

  partial def evalLetArgs (envr: IO.Ref Env) (args : List Types) : IO (IO.Ref Env) := do
    let env ← unwrapEnv envr
    match args with
    | [] => return envr
    | [_] => throw (IO.userError "let*: unexpected syntax")
    | x :: y :: rest =>
      match x with
      | Types.symbolVal key =>
        let (updatedEnv, value) ← evalTypes envr y
        let uenv ← unwrapEnv updatedEnv
        evalLetArgs (← wrapEnv (uenv.add (KeyType.strKey key) env.getLevel value)) rest
      | _ => throw (IO.userError "let*: unexpected syntax")

  partial def evalDo (env: IO.Ref Env) (args : List Types) : IO (IO.Ref Env × Types) := do
    -- only return last computation result
    let (newEnv, results) ← evalFuncArgs env args
    if results.length == 0 then return (newEnv, Types.Nil)
    else return (newEnv, results[results.length - 1]!)

  partial def evalIf (env: IO.Ref Env) (args : List Types) : IO (IO.Ref Env × Types) := do
    if args.length < 2 then throw (IO.userError "unexpected syntax")
    else
      let condition := args[0]!
      let thenExpr := args[1]!
      let hasElse := args.length > 2

      let (newEnv, condResp) ← evalTypes env condition
      let cond := match condResp with
      | Types.boolVal v => v
      | Types.Nil => false
      | _ => true
      if cond then evalTypes newEnv thenExpr
      else if hasElse then evalTypes newEnv args[2]!
      else return (newEnv, Types.Nil)

  partial def swapAtom (envr: IO.Ref Env) (lst: List Types) (args: List Types) : IO (IO.Ref Env × Types) := do
  if lst.length < 2 then throw (IO.userError "swap!: >= 2 argument required")
  else
    let first := lst[0]!
    let fn := lst[1]!
    let rest := lst.drop 2
    let env ← unwrapEnv envr
    match args[0]! with
    | Types.symbolVal sym =>
      match fn with
      | Types.funcVal _ =>
        match env.get (KeyType.strKey sym) with
        | none => throw (IO.userError s!"{sym} not found")
        | some (level, _) => match first with
          | Types.atomVal x => match x with
            | Atom.v v =>
              let (_, res) ← evalFuncVal envr fn ([v] ++ rest)
              let newEnv := env.add (KeyType.strKey sym) level (Types.atomVal (Atom.v res))
              return (← wrapEnv newEnv, res)
            | Atom.withmeta v meta =>
              let (_, res) ← evalFuncVal envr fn ([v] ++ rest)
              let newEnv := env.add (KeyType.strKey sym) level (Types.atomVal (Atom.withmeta res meta))
              return (← wrapEnv newEnv, res)
          | x => throw (IO.userError s!"swap!: unexpected symbol: {x.toString true}, expected: atom")
      | x => throw (IO.userError s!"swap!: unexpected symbol: {x.toString true}, expected: function")
    | x => throw (IO.userError s!"swap!: unexpected token: {x.toString true}, expected: symbol")

  partial def eval (env: IO.Ref Env) (lst : List Types) : IO (IO.Ref Env × Types) := do
    if lst.length < 1 then throw (IO.userError "eval: unexpected syntax")
    else
      let ast := lst[0]!
      evalTypes env ast

  partial def evalFnNative (env: IO.Ref Env) (name: String) (results: List Types) (args: List Types): IO (IO.Ref Env × Types) := do
    match name with
    | "+" => sum env results
    | "-" => sub env results
    | "*" => mul env results
    | "/" => div env results
    | "<" => lt env results
    | "<=" => lte env results
    | ">" => gt env results
    | ">=" => gte env results
    | "=" => eq env results false
    | "list" => return (env, Types.listVal results)
    | "count" => countFunc env results
    | "atom" => makeAtom env results
    | "deref" => derefAtom env results
    | "reset!" => resetAtom env results args
    | "swap!" => swapAtom env results args
    | "prn" => prnFunc env results
    | "pr-str" => prStrFunc env results
    | "str" => strFunc env results
    | "println" => printlnFunc env results
    | "eval" => eval env results
    | "slurp" => slurp env results
    | "read-string" =>
      let res ← readString results (← unwrapEnv env) -- readString results Dict.empty
      return (env, res)
    | _ => match results with
        | [x] => match x with
          | Types.listVal x => match name with
            | "list?" => return (env, Types.boolVal true)
            | "empty?" => return (env, Types.boolVal (x.length == 0))
            | _ => return (env, Types.boolVal false)
          | Types.vecVal x => match name with
            | "empty?" => return (env, Types.boolVal ((toList x).length == 0))
            | _ => return (env, Types.boolVal false)
          | Types.atomVal _ => match name with
            | "atom?" => return (env, Types.boolVal true)
            | _ => return (env, Types.boolVal false)
          | _   => return (env, Types.boolVal false)
        | _   => throw (IO.userError s!"'{name}' not found")
end

def READ (input : String): Except String Types :=
  read_str.{u} input

def PRINT (ast : Types): String :=
  pr_str true ast

def rep (env: IO.Ref Env) (input : String): IO (IO.Ref Env × String) := do
  match READ.{u} input with
  | Except.ok result =>
    try
      let (newenv, res) ← evalTypes env result
      return (newenv, PRINT res)
    catch
      | e => return (env, s!"Error: {e}")
  | Except.error err => return (env, s!"Parsing failed: {err}")

def loadMalFns (env: Env) (fndefs: List String): IO (Env × String) := do
  fndefs.foldlM (fun (res : Env × String) fndef => do
    let (ref, msg) := res
    let (newref, newmsg) ← rep.{u} (← wrapEnv ref) fndef
    return (← unwrapEnv newref, s!"{msg}¬{newmsg}")
  ) (env, "")

def fnDefs: List String := [
    "(def! not (fn* (a) (if a false true)))",
    "(def! load-file (fn* (f) (eval (read-string (str \"(do \" (slurp f) \"\nnil)\")))))",
  ]

def main (args : List String) : IO Unit := do
  let (env0, _) ← loadMalFns.{u} (loadFnNativeAll (Env.data 0 Dict.empty)) fnDefs
  let astArgs := (args.map (fun arg => Types.strVal arg))
  let mut env := setSymbol env0 "*ARGV*" (Types.listVal astArgs)

  if args.length > 0 then
    let (_, val) ← rep.{u} (← wrapEnv env) s!"(load-file \"{args[0]!}\")"
    IO.println val
  else

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
      let (newenv, val) ← rep.{u} (← wrapEnv env) value
      IO.println val
      env := ← unwrapEnv newenv
