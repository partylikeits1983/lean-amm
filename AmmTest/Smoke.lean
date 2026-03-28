/-
  AMM Smoke Tests
  ===============
  Regression tests using `example` (checked at build time)
  and `#eval` for interactive inspection.
-/
import Amm.Core
import Amm.Theorems

namespace AMM

/-! ## Test pool -/

/-- A concrete pool: 5 units of X, 10 units of Y. -/
def p0 : Pool := { x := 5, y := 10 }

/-! ## A. Regression tests via `example` -/

/-- Hand-computed: swapping 1 unit of X into (5,10) gives 10/6 = 5/3 of Y. -/
example : amountOutX p0 1 = (5 : ℚ) / 3 := by
  simp [amountOutX, p0]
  norm_num

/-- Invariant preserved on concrete pool. -/
example : k (swapX p0 1) = k p0 := by
  apply k_swapX_eq
  simp [p0]
  norm_num

/-- Hand-computed: swapping 2 units of Y into (5,10) gives 2*5/12 = 5/6 of X. -/
example : amountOutY p0 2 = (5 : ℚ) / 6 := by
  simp [amountOutY, p0]
  norm_num

/-- Invariant preserved for Y swap on concrete pool. -/
example : k (swapY p0 2) = k p0 := by
  apply k_swapY_eq
  simp [p0]
  norm_num

/-- Post-swap Y reserve matches closed form. -/
example : (swapX p0 1).y = 5 * 10 / (5 + 1) := by
  apply swapX_y_closed_form
  norm_num [p0]

/-- Output is nonneg for our test pool. -/
example : 0 ≤ amountOutX p0 1 := by
  apply output_nonneg_swapX
  · exact ⟨by norm_num [p0], by norm_num [p0]⟩
  · norm_num

/-- Output is less than reserve for our test pool. -/
example : amountOutX p0 1 < p0.y := by
  apply output_lt_reserve_swapX
  · exact ⟨by norm_num [p0], by norm_num [p0]⟩
  · norm_num

/-- Pool stays valid after swap. -/
example : Valid (swapX p0 1) := by
  apply valid_swapX
  · exact ⟨by norm_num [p0], by norm_num [p0]⟩
  · norm_num

/-- TVL identity: valueInX = 2x for our test pool. -/
example : valueInX p0 = 2 * p0.x := by
  apply valueInX_eq_two_x
  exact ⟨by norm_num [p0], by norm_num [p0]⟩

/-- Monotonicity: swapping 1 gives ≤ output than swapping 2. -/
example : amountOutX p0 1 ≤ amountOutX p0 2 := by
  apply monotone_amountOutX
  · exact ⟨by norm_num [p0], by norm_num [p0]⟩
  · norm_num
  · norm_num

/-! ## B. `#eval` for interactive inspection -/

#eval p0
#eval amountOutX p0 1
#eval amountOutX p0 2
#eval amountOutX p0 5
#eval swapX p0 1
#eval k p0
#eval k (swapX p0 1)
#eval rateYperX p0
#eval rateYperX (swapX p0 1)
#eval valueInX p0
#eval valueInY p0

end AMM
