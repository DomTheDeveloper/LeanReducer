set -euo pipefail
for module in "$@"; do
  lake env lean -R src -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxHeartbeats=4000000 -DmaxSynthPendingDepth=3 --tstack=400000 \
    -o ".lake/build/lib/lean/$module.olean" "src/$module.lean"
  lake env leanchecker "$module"
done
