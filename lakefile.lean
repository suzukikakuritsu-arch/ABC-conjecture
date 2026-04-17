import Lake
open Lake DSL

package "abc-conjecture"

@[default_target]
lean_lib «AbcConjecture»
-- require mathlib は不要
