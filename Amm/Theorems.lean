/-
  AMM Theorems
  ============
  Formal proofs for the constant-product AMM swap math.
  All proofs use exact rational arithmetic (ℚ) — no rounding, no overflow.

  These theorems verify properties that a Solidity AMM *assumes* but cannot
  prove on-chain. In Solidity the swap function just executes:

    amountOut = (dx * y) / (dx + x);
    Pools[PID].amount0 += amount;
    Pools[PID].amount1 -= uint(amountOut);

  …and hopes the invariant holds. Here we *prove* it does, along with
  several other safety properties that would otherwise require extensive
  fuzz-testing or auditing.
-/
import Amm.Core

namespace AMM

/-! ## 1. Constant-product invariant preservation

  The most important property of any CFMM: **every swap preserves `k = x * y`**.

  In Solidity this is never checked — the contract just trusts the formula.
  Here we prove it algebraically: after applying `swapX` or `swapY`, the
  product of the new reserves equals the product of the old reserves.

  This is the formal equivalent of verifying that the Solidity swap:

    // k_before = amount0 * amount1
    amountOut = (dx * amount1) / (dx + amount0);
    amount0' = amount0 + dx;
    amount1' = amount1 - amountOut;
    // k_after  = amount0' * amount1'  ==  k_before   ✓
-/

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

/-! ## 2. Closed-form post-swap reserves

  After a swap we can express the new reserve in closed form.

  For an X→Y swap with input `dx`:

    y' = x * y / (x + dx)

  This is useful for computing the exact pool state without simulating the
  subtraction `y - amountOut` step by step. In Solidity you would need to
  compute `amountOut` first and then subtract; here we show the direct formula.
-/

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

/-! ## 3. Output nonnegativity

  A swap should never produce a negative output. In Solidity this is
  implicitly enforced by using `uint` (unsigned integers), which would
  revert on underflow. Here we prove it from first principles:

  If the pool is valid (`x > 0`, `y > 0`) and the input is nonneg (`dx ≥ 0`),
  then the output `dy_out = dx * y / (x + dx)` is also nonneg.

  This guarantees the Solidity line `Pools[PID].amount1 -= uint(amountOut)`
  will never underflow (assuming no fees and exact arithmetic).
-/

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

/-! ## 4. Output strictly less than reserve

  A single swap can never drain the entire reserve of the output token.
  No matter how large `dx` is, `amountOutX(dx) < y`.

  Intuitively: as you pour more X in, you get diminishing returns of Y.
  The output asymptotically approaches `y` but never reaches it.

  In Solidity this means `Pools[PID].amount1` can never hit zero from a
  single swap — the pool always retains some liquidity on both sides.

  This is a key safety property: it prevents complete pool drainage.
-/

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

/-! ## 5. Validity preservation

  If a pool starts valid (`x > 0`, `y > 0`) and receives a nonneg swap input,
  the resulting pool is still valid. This means you can chain swaps
  indefinitely without ever breaking the pool.

  In Solidity terms: if the pool was properly initialised via `deposit`,
  no sequence of `swap` calls can corrupt it into an invalid state.
-/

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

/-! ## 6. Monotonicity of output

  Bigger input → bigger output (weakly). If you swap more X in, you get
  at least as much Y out.

  This is an important economic property: there is no perverse incentive
  to split a trade into smaller pieces (ignoring fees). In Solidity AMMs
  with fees, splitting *can* be beneficial, but the no-fee formula is
  monotone.

  Formally: `dx₁ ≤ dx₂  →  amountOutX(dx₁) ≤ amountOutX(dx₂)`
-/

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

/-! ## 7. Price impact — the swap moves the exchange rate

  When you swap X into the pool, X becomes more abundant and Y becomes
  scarcer. The Y-per-X price drops (X got cheaper relative to Y).

  This is the "price impact" that every DEX trader experiences. The larger
  the swap relative to pool size, the worse the rate.

  In the Solidity contract you can observe this by calling `exchangeRate`
  before and after a swap — the rate changes. Here we prove the direction
  of that change: swapping X in *always* decreases `rateYperX = y / x`.
-/

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

/-! ## 8. TVL identities

  In the Solidity contract, Total Value Locked is computed as:

    rate = amountX / amountY;
    tvl  = rate * amountY + amountX;

  For a constant-product pool this always simplifies to `2 * amountX`
  (when denominated in X) or `2 * amountY` (when denominated in Y).

  This is a well-known property: the spot-price valuation of a 50/50
  constant-product pool is always exactly twice each reserve.
-/

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
