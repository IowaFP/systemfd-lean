-- import SystemFD
import Core

def hello : String := "world"

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
