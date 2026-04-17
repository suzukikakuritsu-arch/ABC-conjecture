import Lake
open Lake DSL

package "abc-conjecture" where
  -- 設定を最小限に

@[default_target]
lean_lib «AbcConjecture» where
  -- ファイル名 AbcConjecture.lean と完全に一致させる

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
