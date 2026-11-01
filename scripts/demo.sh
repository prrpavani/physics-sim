#!/usr/bin/env bash
# Runs the demo story against a running backend: `make run`, then `make demo`.
set -euo pipefail

API="${PARADOX_API:-http://127.0.0.1:8787}"
post() { curl -sS -X POST -H 'content-type: application/json' -d "$2" "$API/api/universe/$1"; }
need() { command -v "$1" >/dev/null || { echo "needs $1"; exit 1; }; }
need curl; need python3

field() { python3 -c "
import json, sys
d = json.load(sys.stdin)
for k in sys.argv[1].split('.'):
    d = d[int(k)] if k.isdigit() else d[k]
print(json.dumps(d) if isinstance(d, (dict, list)) else d)" "$1"; }

WORLD='{"bodies":[{"id":0,"position":{"x":"0","y":"0","z":"0"},"velocity":{"x":"1","y":"0","z":"0"}}],"laws":{"gravity":{"x":"0","y":"2","z":"0"},"maxSpeed":"10"}}'
MULTIPLY='{"type":"body","action":{"type":"scaleVelocity","factor":"100"}}'
CLAMP='{"type":"body","action":{"type":"clampVelocity"}}'
LIMITED="{\"type\":\"seq\",\"first\":$MULTIPLY,\"then\":$CLAMP}"
with_rule() { python3 -c "
import json, sys
w = json.loads(sys.argv[1]); w['rules'] = [json.loads(sys.argv[2])]; print(json.dumps(w))" "$WORLD" "$1"; }

echo "== 1. Unusual gravity, speed limit 10, a rule that multiplies velocity then limits it"
R=$(post verify-property "{\"world\":$(with_rule "$LIMITED"),\"property\":\"boundedVelocity\"}")
echo "   status:  $(echo "$R" | field verdicts.0.status)"
echo "   theorem: $(echo "$R" | field verdicts.0.theoremId)"
[ "$(echo "$R" | field verdicts.0.status)" = proven ]

echo "== 2. Random chaos keeps the guarantee, for every seed"
R=$(post random-events '{"seed":42,"count":200,"kind":"safe"}')
echo "   always allowed: $(echo "$R" | field alwaysAllowed), theorem: $(echo "$R" | field theoremId)"

echo "== 3. Remove the limiter and multiply by 100"
R=$(post verify-property "{\"world\":$(with_rule "$MULTIPLY"),\"property\":\"boundedVelocity\"}")
echo "   status: $(echo "$R" | field verdicts.0.status)"
echo "   $(echo "$R" | field verdicts.0.explanation)"
[ "$(echo "$R" | field verdicts.0.status)" = counterexample ]
TRACE=$(echo "$R" | field verdicts.0.counterexample)

echo "== 4. The trace is checked against the formal model, and a tampered copy is refused"
CHECK=$(post check-trace "{\"trace\":$TRACE,\"claim\":\"boundedVelocity\",\"scope\":\"allowed\"}")
echo "   real trace valid:     $(echo "$CHECK" | field valid)"
[ "$(echo "$CHECK" | field valid)" = True ]
BAD=$(python3 -c "
import json, sys
t = json.loads(sys.argv[1]); t['states'][-1]['tick'] += 1; print(json.dumps(t))" "$TRACE")
CHECK=$(post check-trace "{\"trace\":$BAD,\"claim\":\"boundedVelocity\",\"scope\":\"allowed\"}")
echo "   tampered trace valid: $(echo "$CHECK" | field valid)"
[ "$(echo "$CHECK" | field valid)" = False ]

echo "== 5. Protected mode refuses or repairs the unsafe rule"
R=$(post step "{\"world\":$WORLD,\"event\":{\"type\":\"addRule\",\"rule\":$MULTIPLY},\"mode\":\"protected\"}")
echo "   decision: $(echo "$R" | field decision.result), violations: $(echo "$R" | field violations)"
[ "$(echo "$R" | field decision.result)" = repaired ]
R=$(post step "{\"world\":$WORLD,\"event\":{\"type\":\"changeMaxSpeed\",\"value\":\"-1\"},\"mode\":\"protected\"}")
echo "   negative speed limit: $(echo "$R" | field decision.result)"
[ "$(echo "$R" | field decision.result)" = rejected ]

echo "== 6. Layer A: stationary and moving at 5 cannot both be true"
R=$(post check-consistency "{\"world\":$WORLD,\"constraints\":[{\"type\":\"body\",\"quantity\":\"speedSquared\",\"cmp\":\"eq\",\"value\":\"0\"},{\"type\":\"body\",\"quantity\":\"speedSquared\",\"cmp\":\"eq\",\"value\":\"25\"}]}")
echo "   status: $(echo "$R" | field ruleConsistency.status)"
[ "$(echo "$R" | field ruleConsistency.status)" = inconsistent ]

echo "== 7. Layer B: a portal with no destination is missing behaviour"
R=$(post check-consistency "{\"world\":{\"portals\":[{\"entrance\":{\"minX\":\"0\",\"maxX\":\"1\",\"minY\":\"0\",\"maxY\":\"1\",\"minZ\":\"0\",\"maxZ\":\"1\"}}]}}")
echo "   status: $(echo "$R" | field transitionConsistency.status)"
[ "$(echo "$R" | field transitionConsistency.status)" = underspecified ]

echo "== 8. Invent a force law, then break Newton's third law"
LAW='{"type":"div","a":{"type":"mul","a":{"type":"massA"},"b":{"type":"massB"}},"b":{"type":"add","a":{"type":"const","value":"1"},"b":{"type":"distSquared"}}}'
TWO='"bodies":[{"id":0,"position":{"x":"0","y":"0","z":"0"}},{"id":1,"position":{"x":"3","y":"0","z":"0"}}]'
R=$(post audit-laws "{\"world\":{$TWO,\"laws\":{\"gravity\":{\"x\":\"0\",\"y\":\"0\",\"z\":\"0\"},\"pairForce\":$LAW}}}")
echo "   third law on:  $(echo "$R" | field momentumBetweenBodies.status) ($(echo "$R" | field momentumBetweenBodies.theoremId))"
[ "$(echo "$R" | field momentumBetweenBodies.status)" = proven ]
R=$(post audit-laws "{\"world\":{$TWO,\"laws\":{\"gravity\":{\"x\":\"0\",\"y\":\"0\",\"z\":\"0\"},\"pairForce\":$LAW,\"reaction\":\"0\"}}}")
echo "   third law off: $(echo "$R" | field momentumBetweenBodies.status)"
[ "$(echo "$R" | field momentumBetweenBodies.status)" = counterexample ]

echo
echo "Every step gave the expected result."
