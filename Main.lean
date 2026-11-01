import Paradox.Api.Server
import Paradox.Api.Fixtures

open Paradox.Api

/-- `paradox serve [port]` runs the API. `paradox fixtures [dir]` writes fixtures. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["fixtures"] => writeFixtures "shared/fixtures"; return 0
  | ["fixtures", dir] => writeFixtures dir; return 0
  | "serve" :: rest =>
    let port := (rest.head?.bind String.toNat?).getD 8787
    serve port.toUInt16
    return 0
  | _ =>
    IO.eprintln "usage: paradox serve [port] | paradox fixtures [dir]"
    return 1
