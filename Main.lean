import Core

def hello : String := "System FD"

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
