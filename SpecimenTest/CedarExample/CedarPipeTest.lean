import SpecimenTest.CedarExample.CedarWellTypedTermGenerator

/-! Pipe-based I/O test that generates well-typed Cedar expressions and writes them to an output file. -/

def String.containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

-- Test function that writes expr to input pipe and reads from output pipe
def testPipeIO (s s' : Nat) : IO Unit := do
  let inputPath := "/Users/segevem/Downloads/cedar-outputs/input"
  let outputPath := "/Users/segevem/Downloads/cedar-outputs/output"

  -- Generate Cedar expression and write to input pipe
  let (type, expr) ← Plausible.Gen.runUntil none (genWellFormedTypeAndExpr s) s'
  let generatedExpr := toString expr

  let inputHandle ← IO.FS.Handle.mk inputPath IO.FS.Mode.write
  inputHandle.putStrLn generatedExpr
  inputHandle.flush

  -- Read result from output pipe
  let outputHandle ← IO.FS.Handle.mk outputPath IO.FS.Mode.read
  let result ← outputHandle.getLine
  outputHandle.flush

  IO.println s!"Expr: {generatedExpr}\n"
  IO.println s!"Type: {toString type}\n"
  IO.println s!"Result: {result}"

-- Function that takes a user string and sends it through the pipes
def testPipeWithString (userExpr : String) : IO Unit := do
  let inputPath := "/Users/segevem/Downloads/cedar-outputs/input"
  let outputPath := "/Users/segevem/Downloads/cedar-outputs/output"

  -- Write user expression to input pipe
  let inputHandle ← IO.FS.Handle.mk inputPath IO.FS.Mode.write
  inputHandle.putStrLn userExpr
  inputHandle.flush

  -- Read result from output pipe
  let outputHandle ← IO.FS.Handle.mk outputPath IO.FS.Mode.read
  let result ← outputHandle.getLine
  outputHandle.flush
  IO.println result

-- Test function that keeps generating until it finds a parse error using pipes
def testUntilParseErrorWithPipes : IO Unit := do
  let inputPath := "/Users/segevem/Downloads/cedar-outputs/input"
  let outputPath := "/Users/segevem/Downloads/cedar-outputs/output"
  let mut count := 0
  let mut found := false

  while !found && count < 10000 do
    count := count + 1
    let (exprType, expr) ← Plausible.Gen.runUntil none (genWellFormedTypeAndExpr 5) 1
    let exprStr := toString expr

    -- Write expression to input pipe
    let inputHandle ← IO.FS.Handle.mk inputPath IO.FS.Mode.write
    inputHandle.putStrLn exprStr
    inputHandle.flush

    -- Read result from output pipe
    let outputHandle ← IO.FS.Handle.mk outputPath IO.FS.Mode.read
    let result ← outputHandle.getLine
    outputHandle.flush

    -- Check if result indicates an error (assuming error messages contain "error" or "Error")
    if !(result.containsSubstr "exist") && !(result.containsSubstr "duplicate") && (result.containsSubstr "error" || result.containsSubstr "Error") then
      found := true
      IO.println s!"Found parse or type error after {count} attempts:"
      IO.println s!"Expression: {exprStr}"
      IO.println s!"Type: {repr exprType}"
      IO.println s!"Result: {result}"

  if !found then
    IO.println s!"No parse or type errors found in {count} attempts"

#eval testPipeIO 3 1

#eval testUntilParseErrorWithPipes

#eval testPipeIO 6 1

#eval testPipeWithString "if (((0)-(-1))<((1)+(-1))) then (if (! ((Kesha::D::\"Kesha\")==(true))) then (principal) else ({Aaron: {}, })) else (resource)"

#eval testPipeWithString "if (if ((if ((((-1)<=(0))::nil).containsAll(((-1)<=(1))::nil)) then ((if ((-1)<=(-1)) then ((false)::nil) else (((C::::'')==(::'/'))::nil))::((false)::nil)::nil) else (if (if (if ((::::'')==(::::'/')) then ((A::::'/)==(1)) else ((resource) && (resource))) then (() like '') else (if (true) then (false) else (not (action)))) then (resource) else ((((0)==(1))::nil)::nil))).containsAny((if (if (() like '') then (true) else (if (true) then (true) else ({ : principal }principal))) then (if (if (true) then (true) else (({})::{})) then (((::b::'0')==(false))::nil) else ((0)::{})) else (if (false) then (A) else (false)))::((if (true) then (false) else (resource))::nil)::((()==(::'3'))::nil)::nil)) then (if (if ((if ((a) like 'C') then (if (true) then () else ((action) && ({}))) else ()) like '') then (not (if ((::::'/')==(-1)) then ((nil). ) else (false))) else (if (not (if (()==(-1)) then (({}) || (action)) else ((false)==(false)))) then ((-1)::{}) else (if ((1)<(-1)) then ((action).) else ((action).)))) then (not (not (if ((A::'B')==()) then (0) else (false)))) else (nil)) else (if (if (if (if (not (true)) then ({}) else (if ((;::'')==(1)) then ((::::'/') && (action)) else (false))) then ((a::::'')<(true)) else (if ((1)<=(1)) then (if (false) then ({ : 1 }0) else ((::'')==(1))) else ((1)==(::'/')))) then ((nil) || (action)) else (({ : if (false) then (nil) else ({}) }{  : false }{}). )) then ((nil).) else (not (not (if ((action).) then (false) else ((nil) || (1::::''))))))) then (if (principal) then ({}) else ()) else (((if (if ((()::nil).containsAll(()::nil)) then (if ((-1)<=(-1)) then (not (true)) else (not ((:::b::'')==(:::b::'/')))) else (if (false) then (() && (1)) else (not (true)))) then ({ : resource }{}) else (- (1)))::nil)::if (if (if (((-1)::nil).containsAll((1)::nil)) then (if (if ((false)==(::'C')) then (::'a') else (false)) then (nil) else (if (true) then (true) else (resource))) else ((if ((0)==(/::'/')) then (({}) has c) else (EntityType2::',')). )) then (if ((false)==(false)) then (if ((1)<=(0)) then ((0)==(0)) else (true)) else (true)) else ((context) || (-1))) then (((- ((0)*(-1)))::nil)::nil) else (false))"

-- Step 1: Original complex expression
#eval testPipeWithString "{Kesha: if (if (((1) + (0)) < (if (false) then ((action).John) else (-1))) then (true) else (!(principal is EntityType))) then (if (! ((\"D\") like \"*\")) then (if (if (true) then (false) else ({A: \"B\"})) then ((principal) has Aaron) else (if (false) then ({}) else (EntityType1::\"John\"))) else (principal)) else ([] + [])}"

-- Step 2: Simplify (1) + (0) = 1, and false condition takes else branch (-1)
#eval testPipeWithString "{Kesha: if (if (1 < -1) then (true) else ((principal is EntityType1))) then (if (! ((\"D\") like \"*\")) then (if (if (true) then (false) else ({A: \"B\"})) then ((principal) has Aaron) else (if (false) then ({}) else (EntityType1::\"John\"))) else (principal)) else (([]) + ({}))}"

-- Step 3: 1 < -1 is false, so take else branch
#eval testPipeWithString "{Kesha: if (principal is EntityType1) then (if (! ((\"D\") like \"*\")) then (if (if (true) then (false) else ({A: \"B\"})) then ((principal) has Aaron) else (if (false) then ({}) else (EntityType1::\"John\"))) else (principal)) else (([]) + ({}))}"

-- Step 4: Assume principal is not EntityType1, so condition is false, take else branch
#eval testPipeWithString "{Kesha: ([]) + ({})}"

-- Step 5: The type error - adding set to record
#eval testPipeWithString "([]) + ({})"
