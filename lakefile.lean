import Lake
open Lake DSL

package "abc_conjecture" where
  -- パッケージの設定

@[default_target]
lean_lib «AbcConjecture» where
  -- ライブラリの設定（ファイル名に合わせて変更してください）

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
