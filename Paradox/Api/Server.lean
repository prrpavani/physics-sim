import Std.Http
import Paradox.Api.Routes

/-!
# The HTTP server

This only moves bytes between the network and `handle`. All decisions are made by `handle`, which
calls the formal model. Requests are limited in size, and the server binds to this machine only.
-/

namespace Paradox.Api

open Std Async Http

/-- The largest request body accepted, in bytes. -/
def maxRequestBytes : Nat := 8 * 1024 * 1024

/-- The content type for a built frontend file. -/
def contentType (file : String) : String :=
  if file.endsWith ".js" then "text/javascript; charset=utf-8"
  else if file.endsWith ".css" then "text/css; charset=utf-8"
  else if file.endsWith ".json" then "application/json"
  else if file.endsWith ".svg" then "image/svg+xml"
  else if file.endsWith ".woff2" then "font/woff2"
  else if file.endsWith ".woff" then "font/woff"
  else if file.endsWith ".png" then "image/png"
  else "text/html; charset=utf-8"

/-- The file for a request path: plain paths inside `web/` with a known extension. -/
def staticPath (route : String) : Option String :=
  let path := if route == "/" then "/index.html" else route
  let noParentDirs := (path.splitOn "..").length == 1
  let known := [".html", ".js", ".css", ".json", ".svg", ".woff2", ".woff", ".png"].any (fun ext => path.endsWith ext)
  if noParentDirs && known then some s!"web{path}" else none

/-- The text of the files holding the proofs the app shows. -/
def proofSources : IO (List String) :=
  ["Paradox/Proofs.lean", "Paradox/Verdict.lean"].mapM fun f => do
    try IO.FS.readFile f catch _ => pure ""

/-- Serve the API on this machine until the process is stopped. -/
def serve (port : UInt16) : IO Unit := Async.block do
  let handler := Server.Handler.ofFn fun req => do
    let target := toString req.line.uri
    let path := (target.splitOn "?").headD target
    let method := toString req.line.method
    if !path.startsWith "/api/" && method == "GET" then
      match staticPath path with
      | some file =>
        try
          let bytes ← (IO.FS.readBinFile file : IO ByteArray)
          Response.ok |>.header! "Content-Type" (contentType file) |>.fromBytes bytes
        catch _ => Response.notFound |>.text "not found. Run `make frontend` to build the UI."
      | none => Response.notFound |>.text "not found"
    else if method == "OPTIONS" then
      Response.ok
        |>.header! "Access-Control-Allow-Origin" "*"
        |>.header! "Access-Control-Allow-Methods" "GET, POST, OPTIONS"
        |>.header! "Access-Control-Allow-Headers" "content-type"
        |>.text ""
    else
      let body : String ← req.body.readAll (maximumSize := some (.ofNat maxRequestBytes))
      let sources ← if path == "/api/proofs" then proofSources else pure []
      let reply := handle method path body sources
      let builder := match reply.code with
        | 200 => Response.ok
        | 404 => Response.notFound
        | _ => Response.badRequest
      builder
        |>.header! "Access-Control-Allow-Origin" "*"
        |>.json reply.body.compress
  let addr : Net.SocketAddress := .v4 (.mk (.ofParts 127 0 0 1) port)
  let _server ← Server.serve addr handler
  IO.println s!"PARADOX is running at http://127.0.0.1:{port}"
  repeat
    Async.sleep 3600000

end Paradox.Api
