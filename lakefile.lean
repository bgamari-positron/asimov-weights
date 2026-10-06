import Lake
open Lake DSL

package «asimov-weights» where
  leanOptions := #[⟨`warningAsError, true⟩]
  testDriver := "asimov_weights_tests"

require «asimov-lean» from "../asimov-sw/asimov-lean"

@[default_target]
lean_lib AsimovWeights

lean_exe «asimov_weights_tests» where
  root := `Tests
