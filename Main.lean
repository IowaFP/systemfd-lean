import SystemFD
import Hs

def hello : String := "world"

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
