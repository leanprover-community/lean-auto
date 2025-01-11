abbrev EvalProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

def EvalProc.create (path : String) (args : Array String) : IO EvalProc :=
  IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped, cmd := path, args := args}
