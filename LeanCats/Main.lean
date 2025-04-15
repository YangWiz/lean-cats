import Init.System.IO

def get_file(path: System.FilePath) : IO String := do
  let file <- IO.FS.readFile path
  sorry
