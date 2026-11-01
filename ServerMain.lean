import Std.Http
import Paradox.Api

/-!
# The PARADOX web server

Serves the browser files in `web/` and the API. The API runs the Lean transition function
`step`; the browser only draws what it returns.
-/

open Std Async Http
open Lean (Json)
open Paradox.Api

def contentType (file : String) : String :=
  if file.endsWith ".js" then "text/javascript; charset=utf-8"
  else if file.endsWith ".css" then "text/css; charset=utf-8"
  else if file.endsWith ".json" then "application/json"
  else "text/html; charset=utf-8"

/-- Only plain paths inside `web/` with a known extension. -/
def staticPath (route : String) : Option String :=
  let path := if route == "/" then "/index.html" else route
  let noParentDirs := (path.splitOn "..").length == 1
  if noParentDirs && [".html", ".js", ".css", ".json"].any (fun ext => path.endsWith ext) then some s!"web{path}"
  else none

def seedOf (query : String) : Nat :=
  let pairs := (query.splitOn "&").filterMap fun p =>
    match p.splitOn "=" with | [k, v] => some (k, v) | _ => none
  (((pairs.find? (·.1 == "seed")).bind (·.2.toNat?)).getD 1) % 1000000000

def jsonResponse (j : Json) : ContextAsync (Response Body.Any) :=
  Response.ok |>.header! "Content-Type" "application/json" |>.fromBytes j.compress.toUTF8

def handler : Server.StatelessHandler := Server.Handler.ofFn fun req => do
  let route := toString req.line.uri.path
  let query := (toString req.line.uri.query).dropWhile (· == '?') |>.toString
  if route == "/api/world" then
    jsonResponse (Json.mkObj [("world", generateWorld (seedOf query))])
  else if route == "/api/step" then
    let text : String ← req.body.readAll (maximumSize := some 8000000)
    match Json.parse text >>= stepRequest with
    | .ok answer => jsonResponse answer
    | .error msg => jsonResponse (Json.mkObj [("error", msg)])
  else
    match staticPath route with
    | some file =>
      try
        let bytes ← (IO.FS.readBinFile file : IO ByteArray)
        Response.ok |>.header! "Content-Type" (contentType file) |>.fromBytes bytes
      catch _ => Response.notFound |>.text "not found"
    | none => Response.notFound |>.text "not found"

def main (args : List String) : IO Unit := do
  let port : UInt16 := ((args.head? >>= String.toNat?).getD 8000).toUInt16
  Async.block do
    let addr : Net.SocketAddress := .v4 (.mk (.ofParts 127 0 0 1) port)
    let server ← Std.Http.Server.serve addr handler
    IO.println s!"PARADOX is running at http://127.0.0.1:{port}"
    (← IO.getStdout).flush
    server.waitShutdown
