/-
  AMM Core Definitions
  ====================
  Pure constant-product AMM model over exact rationals (ℚ).
  No blockchain plumbing, no LP accounting — just math.
-/
import Mathlib

namespace AMM

/-! ## Pool state -/

/-- A constant-product pool holding reserves of two assets. -/
structure Pool where
  x : ℚ
  y : ℚ
deriving Repr, DecidableEq

/-! ## Validity predicate -/

/-- A pool is valid when both reserves are strictly positive. -/
def Valid (p : Pool) : Prop :=
  0 < p.x ∧ 0 < p.y

/-! ## Invariant -/

/-- The constant-product invariant `k = x * y`. -/
def k (p : Pool) : ℚ :=
  p.x * p.y

/-! ## Spot prices -/

/-- Spot price: how much X per unit of Y. -/
def rateXperY (p : Pool) : ℚ :=
  p.x / p.y

/-- Spot price: how much Y per unit of X. -/
def rateYperX (p : Pool) : ℚ :=
  p.y / p.x

/-! ## Swap output formulas -/

/-- Exact no-fee output of Y when swapping `dx` units of X into the pool.
    Formula: `dy_out = dx * y / (x + dx)` -/
def amountOutX (p : Pool) (dx : ℚ) : ℚ :=
  dx * p.y / (p.x + dx)

/-- Exact no-fee output of X when swapping `dy` units of Y into the pool.
    Formula: `dx_out = dy * x / (y + dy)` -/
def amountOutY (p : Pool) (dy : ℚ) : ℚ :=
  dy * p.x / (p.y + dy)

/-! ## Swap operations -/

/-- Pool state after swapping `dx` of X in.
    New reserves: `x' = x + dx`, `y' = y - amountOutX(dx)`. -/
def swapX (p : Pool) (dx : ℚ) : Pool :=
  { x := p.x + dx
    y := p.y - amountOutX p dx }

/-- Pool state after swapping `dy` of Y in.
    New reserves: `x' = x - amountOutY(dy)`, `y' = y + dy`. -/
def swapY (p : Pool) (dy : ℚ) : Pool :=
  { x := p.x - amountOutY p dy
    y := p.y + dy }

/-! ## Auxiliary operations (not LP accounting) -/

/-- Arbitrary reserve mutation. This is NOT proper LP-share accounting;
    it just adds to both reserves. -/
def deposit (p : Pool) (dx dy : ℚ) : Pool :=
  { x := p.x + dx
    y := p.y + dy }

/-- Pool value at spot price, denominated in X.
    Note: for a valid pool, `valueInX p = 2 * p.x` exactly. -/
def valueInX (p : Pool) : ℚ :=
  p.x + rateXperY p * p.y

/-- Pool value at spot price, denominated in Y.
    Note: for a valid pool, `valueInY p = 2 * p.y` exactly. -/
def valueInY (p : Pool) : ℚ :=
  p.y + rateYperX p * p.x

end AMM
