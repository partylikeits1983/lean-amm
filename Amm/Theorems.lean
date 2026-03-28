/-
  AMM Theorems
  ============
  Formal proofs for the constant-product AMM.
  All proofs use exact rational arithmetic (ℚ).
-/
import Amm.Core

namespace AMM

/-! ## 1. Constant-product invariant preservation -/

/-- Swapping X into the pool preserves the constant product `k = x * y`. -/
theorem k_swapX_eq (p : Pool) (dx : ℚ) (h : p.x + dx ≠ 0) :
    k (swapX p dx) = k p := by
  simp only [k, swapX, amountOutX]
  field_simp
  ring

/-- Swapping Y into the pool preserves the constant product `k = x * y`. -/
theorem k_swapY_eq (p : Pool) (dy : ℚ) (h : p.y + dy ≠ 0) :
    k (swapY p dy) = k p := by
  simp only [k, swapY, amountOutY]
  field_simp
  ring

/-! ## 2. Closed-form post-swap reserves -/

/-- After swapping `dx` of X in, the new Y reserve is `x * y / (x + dx)`. -/
theorem swapX_y_closed_form (p : Pool) (dx : ℚ) (h : p.x + dx ≠ 0) :
    (swapX p dx).y = p.x * p.y / (p.x + dx) := by
  simp only [swapX, amountOutX]
  field_simp
  ring

/-- After swapping `dy` of Y in, the new X reserve is `y * x / (y + dy)`. -/
theorem swapY_x_closed_form (p : Pool) (dy : ℚ) (h : p.y + dy ≠ 0) :
    (swapY p dy).x = p.y * p.x / (p.y + dy) := by
  simp only [swapY, amountOutY]
  field_simp
  ring

/-! ## 3. Output nonnegativity -/

/-- If the pool is valid and `dx ≥ 0`, the output is nonneg. -/
theorem output_nonneg_swapX (p : Pool) (dx : ℚ)
    (hv : Valid p) (hdx : 0 ≤ dx) :
    0 ≤ amountOutX p dx := by
  simp only [amountOutX]
  apply div_nonneg
  · exact mul_nonneg hdx (le_of_lt hv.2)
  · linarith [hv.1]

/-- Symmetric: if the pool is valid and `dy ≥ 0`, the output is nonneg. -/
theorem output_nonneg_swapY (p : Pool) (dy : ℚ)
    (hv : Valid p) (hdy : 0 ≤ dy) :
    0 ≤ amountOutY p dy := by
  simp only [amountOutY]
  apply div_nonneg
  · exact mul_nonneg hdy (le_of_lt hv.1)
  · linarith [hv.2]

/-! ## 4. Output strictly less than reserve -/

/-- The output of a swap never drains the entire reserve. -/
theorem output_lt_reserve_swapX (p : Pool) (dx : ℚ)
    (hv : Valid p) (hdx : 0 ≤ dx) :
    amountOutX p dx < p.y := by
  simp only [amountOutX]
  have hden : 0 < p.x + dx := by linarith [hv.1]
  rw [div_lt_iff₀ hden]
  nlinarith [hv.1, hv.2]

/-- Symmetric: output of Y→X swap is strictly less than X reserve. -/
theorem output_lt_reserve_swapY (p : Pool) (dy : ℚ)
    (hv : Valid p) (hdy : 0 ≤ dy) :
    amountOutY p dy < p.x := by
  simp only [amountOutY]
  have hden : 0 < p.y + dy := by linarith [hv.2]
  rw [div_lt_iff₀ hden]
  nlinarith [hv.1, hv.2]

/-! ## 5. Validity preservation -/

/-- A valid pool remains valid after an X→Y swap with nonneg input. -/
theorem valid_swapX (p : Pool) (dx : ℚ)
    (hv : Valid p) (hdx : 0 ≤ dx) :
    Valid (swapX p dx) := by
  constructor
  · simp only [swapX]
    linarith [hv.1]
  · rw [swapX_y_closed_form p dx (by linarith [hv.1] : p.x + dx ≠ 0)]
    apply div_pos
    · exact mul_pos hv.1 hv.2
    · linarith [hv.1]

/-- Symmetric: a valid pool remains valid after a Y→X swap. -/
theorem valid_swapY (p : Pool) (dy : ℚ)
    (hv : Valid p) (hdy : 0 ≤ dy) :
    Valid (swapY p dy) := by
  constructor
  · rw [swapY_x_closed_form p dy (by linarith [hv.2] : p.y + dy ≠ 0)]
    apply div_pos
    · exact mul_pos hv.2 hv.1
    · linarith [hv.2]
  · simp only [swapY]
    linarith [hv.2]

/-! ## 6. Monotonicity of output -/

/-- More input gives (weakly) more output: `dx₁ ≤ dx₂ → out(dx₁) ≤ out(dx₂)`. -/
theorem monotone_amountOutX (p : Pool) (dx₁ dx₂ : ℚ)
    (hv : Valid p) (h1 : 0 ≤ dx₁) (h12 : dx₁ ≤ dx₂) :
    amountOutX p dx₁ ≤ amountOutX p dx₂ := by
  simp only [amountOutX]
  have hd1 : (0 : ℚ) < p.x + dx₁ := by linarith [hv.1]
  have hd2 : (0 : ℚ) < p.x + dx₂ := by linarith [hv.1]
  rw [div_le_div_iff₀ hd1 hd2]
  -- Goal: dx₁ * p.y * (p.x + dx₂) ≤ dx₂ * p.y * (p.x + dx₁)
  -- Expand: dx₁ * p.y * p.x + dx₁ * p.y * dx₂ ≤ dx₂ * p.y * p.x + dx₂ * p.y * dx₁
  -- The cross terms dx₁ * p.y * dx₂ = dx₂ * p.y * dx₁ cancel
  -- So need: dx₁ * p.y * p.x ≤ dx₂ * p.y * p.x
  -- Which follows from dx₁ ≤ dx₂ and p.y * p.x ≥ 0
  have hpypx : 0 ≤ p.y * p.x := le_of_lt (mul_pos hv.2 hv.1)
  nlinarith [mul_le_mul_of_nonneg_right h12 hpypx]

/-- Symmetric monotonicity for Y→X swaps. -/
theorem monotone_amountOutY (p : Pool) (dy₁ dy₂ : ℚ)
    (hv : Valid p) (h1 : 0 ≤ dy₁) (h12 : dy₁ ≤ dy₂) :
    amountOutY p dy₁ ≤ amountOutY p dy₂ := by
  simp only [amountOutY]
  have hd1 : (0 : ℚ) < p.y + dy₁ := by linarith [hv.2]
  have hd2 : (0 : ℚ) < p.y + dy₂ := by linarith [hv.2]
  rw [div_le_div_iff₀ hd1 hd2]
  have hpxpy : 0 ≤ p.x * p.y := le_of_lt (mul_pos hv.1 hv.2)
  nlinarith [mul_le_mul_of_nonneg_right h12 hpxpy]

/-! ## 7. Price movement with explicit quote convention -/

/-- Swapping X into the pool decreases the Y-per-X rate (X becomes cheaper).
    Convention: `rateYperX = y / x`. After adding X, this ratio drops. -/
theorem rateYperX_decreases_after_swapX (p : Pool) (dx : ℚ)
    (hv : Valid p) (hdx : 0 < dx) :
    rateYperX (swapX p dx) < rateYperX p := by
  simp only [rateYperX]
  rw [swapX_y_closed_form p dx (by linarith [hv.1] : p.x + dx ≠ 0)]
  simp only [swapX]
  have hx : (0 : ℚ) < p.x := hv.1
  have hxdx : (0 : ℚ) < p.x + dx := by linarith
  rw [div_div]
  rw [div_lt_div_iff₀ (mul_pos hxdx hxdx) hx]
  -- Goal: p.x * p.y * p.x < p.y * ((p.x + dx) * (p.x + dx))
  -- Factor out p.y > 0: need p.x * p.x < (p.x + dx) * (p.x + dx)
  -- i.e. p.x² < (p.x + dx)²
  -- Since p.x > 0 and dx > 0, p.x < p.x + dx, so p.x² < (p.x + dx)²
  have hpy : 0 < p.y := hv.2
  have hlt : p.x < p.x + dx := by linarith
  have hpx_pos : 0 < p.x := hv.1
  have hxdx_pos : 0 < p.x + dx := by linarith
  have hsq : p.x * p.x < (p.x + dx) * (p.x + dx) :=
    mul_lt_mul hlt (le_of_lt hlt) hpx_pos (le_of_lt hxdx_pos)
  nlinarith

/-- Swapping Y into the pool decreases the X-per-Y rate (Y becomes cheaper).
    Convention: `rateXperY = x / y`. After adding Y, this ratio drops. -/
theorem rateXperY_decreases_after_swapY (p : Pool) (dy : ℚ)
    (hv : Valid p) (hdy : 0 < dy) :
    rateXperY (swapY p dy) < rateXperY p := by
  simp only [rateXperY]
  rw [swapY_x_closed_form p dy (by linarith [hv.2] : p.y + dy ≠ 0)]
  simp only [swapY]
  have hy : (0 : ℚ) < p.y := hv.2
  have hydy : (0 : ℚ) < p.y + dy := by linarith
  rw [div_div]
  rw [div_lt_div_iff₀ (mul_pos hydy hydy) hy]
  -- Goal: p.y * p.x * p.y < p.x * ((p.y + dy) * (p.y + dy))
  have hpx : 0 < p.x := hv.1
  have hlt : p.y < p.y + dy := by linarith
  have hy_pos : 0 < p.y := hv.2
  have hydy_pos : 0 < p.y + dy := by linarith
  have hsq : p.y * p.y < (p.y + dy) * (p.y + dy) :=
    mul_lt_mul hlt (le_of_lt hlt) hy_pos (le_of_lt hydy_pos)
  nlinarith

/-! ## 8. TVL identities -/

/-- For a valid pool, `valueInX = 2 * x`. -/
theorem valueInX_eq_two_x (p : Pool) (hv : Valid p) :
    valueInX p = 2 * p.x := by
  simp only [valueInX, rateXperY]
  have hy : p.y ≠ 0 := ne_of_gt hv.2
  field_simp
  ring

/-- For a valid pool, `valueInY = 2 * y`. -/
theorem valueInY_eq_two_y (p : Pool) (hv : Valid p) :
    valueInY p = 2 * p.y := by
  simp only [valueInY, rateYperX]
  have hx : p.x ≠ 0 := ne_of_gt hv.1
  field_simp
  ring

end AMM
