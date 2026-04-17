import Lake
open Lake DSL

package "abc-conjecture" where
  -- パッケージ設定

@[default_target]
lean_lib «AbcConjecture» where
  -- AbcConjecture.lean をビルド対象に指定

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
