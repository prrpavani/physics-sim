import Paradox.Api.Server

/-- `paradox serve [port]` runs the app. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "serve" :: rest =>
    Paradox.Api.serve ((rest.head?.bind String.toNat?).getD 8787).toUInt16
    return 0
  | _ =>
    IO.eprintln "usage: paradox serve [port]"
    return 1
