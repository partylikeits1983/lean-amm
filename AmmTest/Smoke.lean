/-
  AMM Smoke Tests
  ===============
  Regression tests using `example` (checked at build time)
  and `#eval` for interactive inspection.

  These tests exercise only the swap math — the same formulas that
  the Solidity `swap` function uses:

    amountOut = (dx * y) / (dx + x)
-/
import Amm.Core
import Amm.Theorems

namespace AMM

-- ============================================================================
-- Test Pool 1: small pool (5 X, 10 Y) — matches the Solidity comment example
-- ============================================================================

/-! ## Test pool (small) -/

/-- A concrete pool: 5 units of X, 10 units of Y.
    k = 5 * 10 = 50 -/
def p0 : Pool := { x := 5, y := 10 }

/-! ## A. Regression tests via `example` -/

/-- Hand-computed: swapping 1 unit of X into (5,10) gives 10/6 = 5/3 of Y.
    Derivation (from the Solidity comments):
      k = 50, dx = 1
      50 = (5+1) * (10+dy)  →  dy = -10/6  →  amountOut = 10/6 = 5/3 -/
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

/-! ## B. `#eval` for interactive inspection (small pool) -/

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

-- ============================================================================
-- Test Pool 2: 100 X × 100 Y — swap 10 X for Y
-- ============================================================================
-- This is the main requested test scenario.
--
-- Pool:  x = 100, y = 100, k = 10000
-- Swap:  dx = 10 (user sends 10 units of X)
--
-- amountOut = dx * y / (x + dx)
--           = 10 * 100 / (100 + 10)
--           = 1000 / 110
--           = 100/11
--           ≈ 9.0909...
--
-- Post-swap pool:
--   x' = 100 + 10 = 110
--   y' = 100 - 100/11 = 1000/11 ≈ 90.909...
--   k' = 110 * 1000/11 = 10000 = k  ✓
-- ============================================================================

/-! ## Test pool (100 × 100) -/

/-- A balanced pool: 100 units of X, 100 units of Y.
    k = 100 * 100 = 10000.  Exchange rate = 1:1. -/
def p1 : Pool := { x := 100, y := 100 }

/-! ## C. Swap 10 X for Y — exact value checks -/

/-- Swapping 10 X into (100, 100) yields exactly 100/11 ≈ 9.0909 of Y.
    amountOut = 10 * 100 / (100 + 10) = 1000 / 110 = 100/11 -/
example : amountOutX p1 10 = (100 : ℚ) / 11 := by
  simp [amountOutX, p1]
  norm_num

/-- The constant product is preserved: k stays at 10000. -/
example : k (swapX p1 10) = k p1 := by
  apply k_swapX_eq
  simp [p1]; norm_num

/-- After the swap, X reserve is 110. -/
example : (swapX p1 10).x = 110 := by
  simp [swapX, p1]; norm_num

/-- After the swap, Y reserve is 1000/11 ≈ 90.909. -/
example : (swapX p1 10).y = (1000 : ℚ) / 11 := by
  simp [swapX, amountOutX, p1]; norm_num

/-- Output is nonneg. -/
example : 0 ≤ amountOutX p1 10 := by
  apply output_nonneg_swapX
  · exact ⟨by norm_num [p1], by norm_num [p1]⟩
  · norm_num

/-- Output (100/11 ≈ 9.09) is strictly less than the Y reserve (100). -/
example : amountOutX p1 10 < p1.y := by
  apply output_lt_reserve_swapX
  · exact ⟨by norm_num [p1], by norm_num [p1]⟩
  · norm_num

/-- Pool remains valid after the swap. -/
example : Valid (swapX p1 10) := by
  apply valid_swapX
  · exact ⟨by norm_num [p1], by norm_num [p1]⟩
  · norm_num

/-- Price impact: Y-per-X rate drops after swapping X in.
    Before: 100/100 = 1.0   After: (1000/11)/110 = 1000/1210 ≈ 0.826 -/
example : rateYperX (swapX p1 10) < rateYperX p1 := by
  apply rateYperX_decreases_after_swapX
  · exact ⟨by norm_num [p1], by norm_num [p1]⟩
  · norm_num

/-! ## D. `#eval` — print swap results to terminal

  Pool: 100 X × 100 Y
  Swap: 10 X → ? Y
-/

-- Pool before swap
#eval IO.println "═══════════════════════════════════════════════"
#eval IO.println "Pool: 100 X × 100 Y   |   Swap: 10 X → ? Y"
#eval IO.println "═══════════════════════════════════════════════"

#eval do
  let pool : Pool := p1
  IO.println s!"Pool before swap:  x = {pool.x}, y = {pool.y}"
  IO.println s!"k before swap:     {k pool}"
  IO.println s!"Rate Y/X before:   {rateYperX pool}"

#eval do
  let pool : Pool := p1
  let dx : ℚ := 10
  let dy := amountOutX pool dx
  let poolAfter := swapX pool dx
  IO.println s!"Swap input (dx):   {dx}"
  IO.println s!"Swap output (dy):  {dy}  (≈ {dy.num}/{dy.den})"
  IO.println s!"Pool after swap:   x = {poolAfter.x}, y = {poolAfter.y}"
  IO.println s!"k after swap:      {k poolAfter}"
  IO.println s!"Rate Y/X after:    {rateYperX poolAfter}"

#eval IO.println "═══════════════════════════════════════════════"

-- Additional #eval for quick inspection
#eval amountOutX p1 10       -- should print 100/11
#eval swapX p1 10            -- should print { x := 110, y := 1000/11 }
#eval k p1                   -- should print 10000
#eval k (swapX p1 10)        -- should print 10000 (invariant preserved!)

-- ============================================================================
-- Test Pool 3: larger swap — 50 X into (100, 100)
-- ============================================================================
-- amountOut = 50 * 100 / (100 + 50) = 5000 / 150 = 100/3 ≈ 33.33
-- Even swapping half the reserve, you only get a third of Y out.
-- This demonstrates the diminishing returns / price impact of large swaps.

/-! ## E. Large swap: 50 X into (100, 100) -/

/-- Swapping 50 X into (100, 100) yields 100/3 ≈ 33.33 of Y.
    Note: you put in 50% of the X reserve but only get 33% of Y. -/
example : amountOutX p1 50 = (100 : ℚ) / 3 := by
  simp [amountOutX, p1]
  norm_num

/-- k is still preserved for the large swap. -/
example : k (swapX p1 50) = k p1 := by
  apply k_swapX_eq
  simp [p1]; norm_num

#eval do
  IO.println "── Large swap: 50 X into (100, 100) ──"
  let dy := amountOutX p1 50
  IO.println s!"Swap 50 X → {dy} Y  (≈ 33.33)"
  IO.println s!"Price impact is significant: 50% of X reserve in, only 33% of Y out"

end AMM
