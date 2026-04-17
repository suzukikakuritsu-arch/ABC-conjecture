import Lake
open Lake DSL

package «abc-conjecture» where
  -- 設定なし

@[default_target]
lean_lib «AbcConjecture» where
  -- ここがファイル名 (AbcConjecture.lean) と一致している必要があります

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
