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

/-- Serve the API on this machine until the process is stopped. -/
def serve (port : UInt16) : IO Unit := Async.block do
  let handler := Server.Handler.ofFn fun req => do
    let target := toString req.line.uri
    let path := (target.splitOn "?").headD target
    let method := toString req.line.method
    if method == "OPTIONS" then
      Response.ok
        |>.header! "Access-Control-Allow-Origin" "*"
        |>.header! "Access-Control-Allow-Methods" "GET, POST, OPTIONS"
        |>.header! "Access-Control-Allow-Headers" "content-type"
        |>.text ""
    else
      let body : String ← req.body.readAll (maximumSize := some (.ofNat maxRequestBytes))
      let reply := handle method path body
      let builder := match reply.code with
        | 200 => Response.ok
        | 404 => Response.notFound
        | _ => Response.badRequest
      builder
        |>.header! "Access-Control-Allow-Origin" "*"
        |>.json reply.body.compress
  let addr : Net.SocketAddress := .v4 (.mk (.ofParts 127 0 0 1) port)
  let _server ← Server.serve addr handler
  IO.println s!"PARADOX backend on http://127.0.0.1:{port} (contract {contractVersion})"
  repeat
    Async.sleep 3600000

end Paradox.Api
