import Lake
open Lake DSL

package ExponentialRamsey where
  leanOptions := #[
    ⟨`autoImplicit, false⟩, -- prevents typos to be interpreted as new free variables
    ⟨`relaxedAutoImplicit, false⟩] -- prevents typos to be interpreted as new free variables
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

@[default_target]
lean_lib ExponentialRamsey
