import Feline

def bufsize : USize := 20 * 1024

partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File no found {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args

def usage : IO UInt32 := do
  let stdout ← IO.getStdout
  stdout.putStrLn "Usage: feline [OPTION]... [FILE]..."
  stdout.putStrLn "With no FILE, or when FILE is -, read standard input."
  stdout.putStrLn "\t--help\tdisplay this help and exit"
  pure 0

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | "--help" :: _ => usage
  | _ => process 0 args
