import ABC.Core
import ABC.Arithmetic
import ABC.Analytic

namespace ABC

theorem abc_final :
  abc_conjecture := by
  intro t ε hε
  use 1
  exact epsilon_control t ε hε

end ABC
