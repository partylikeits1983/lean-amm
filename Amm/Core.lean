/-
  AMM Core Definitions
  ====================
  Pure constant-product AMM model over exact rationals (ℚ).
  No blockchain plumbing, no LP accounting — just the swap math.

  This mirrors the core swap logic from a Solidity CFMM (Constant Function
  Market Maker) such as:

    contract AMM {
      struct Pool { address token0; address token1; uint amount0; uint amount1; }
      mapping(uint => Pool) public Pools;
      ...
    }

  In Solidity the pool state is two unsigned integers (`amount0`, `amount1`)
  stored on-chain. Here we model the same pair of reserves as rational numbers
  so that every arithmetic step is exact — no rounding, no overflow.
-/
import Mathlib

namespace AMM

/-! ## Pool state

  In Solidity a pool is a struct with two token reserves:

    struct Pool {
      address token0;
      address token1;
      uint amount0;   // ← reserve X
      uint amount1;   // ← reserve Y
    }

  We strip away the addresses and ERC-20 plumbing and keep only the two
  reserve balances, modelled as rationals (ℚ) for exact arithmetic.
-/

/-- A constant-product pool holding reserves of two assets.
    Equivalent to `(amount0, amount1)` in the Solidity `Pool` struct. -/
structure Pool where
  x : ℚ   -- reserve of token X  (Solidity: `Pools[PID].amount0`)
  y : ℚ   -- reserve of token Y  (Solidity: `Pools[PID].amount1`)
deriving Repr, DecidableEq

/-! ## Validity predicate

  In Solidity we guard against uninitialised pools with:

    require(token0 != address(0), "not initialized X");
    require(token1 != address(0), "not initialized Y");

  The mathematical equivalent is requiring both reserves to be strictly
  positive. This is the precondition that makes every formula well-defined.
-/

/-- A pool is valid when both reserves are strictly positive. -/
def Valid (p : Pool) : Prop :=
  0 < p.x ∧ 0 < p.y

/-! ## Constant-product invariant

  The fundamental rule of a CFMM:

    X * Y = K

  Every swap must preserve this product. In Solidity the invariant is
  maintained implicitly by the swap formula; here we define `k` explicitly
  so we can *prove* it is preserved (see `Theorems.lean`).
-/

/-- The constant-product invariant `k = x * y`. -/
def k (p : Pool) : ℚ :=
  p.x * p.y

/-! ## Spot prices / exchange rates

  In the Solidity contract the exchange rate is computed as:

    function exchangeRate(uint PID, address token0) public view returns (uint rate) {
      rate = uint(amountX.div(amountY));
    }

  Here we define both directions of the rate as simple rational division.
  Because we use ℚ, these are exact — no fixed-point truncation.
-/

/-- Spot price: how much X per unit of Y.  `rate = x / y`
    (Solidity: `exchangeRate` when quoting token0 in terms of token1) -/
def rateXperY (p : Pool) : ℚ :=
  p.x / p.y

/-- Spot price: how much Y per unit of X.  `rate = y / x`
    (Solidity: `exchangeRate` when quoting token1 in terms of token0) -/
def rateYperX (p : Pool) : ℚ :=
  p.y / p.x

/-! ## Swap output formulas

  The heart of the AMM. In the Solidity contract the swap output is:

    amountOut = (dx * y) / (dx + x)

  ### Derivation (worked example from the Solidity comments):
  ```
    x  = 5,  y  = 10
    k  = x * y = 50
    dx = 1                          -- user sends 1 unit of X

    k = (x + dx) * (y + dy)        -- invariant must hold after swap
    50 = (5 + 1) * (10 + dy)
    50 = 6 * (10 + dy)
    50 = 60 + 6·dy
    -10 = 6·dy
    dy = -10/6 ≈ -1.667            -- negative means Y leaves the pool

    amountOut = -dy = 10/6 = 5/3
  ```

  Rearranging in general:

    dy_out = dx * y / (x + dx)

  This is exactly what `amountOutX` computes below.
-/

/-- Exact no-fee output of Y when swapping `dx` units of X into the pool.
    Formula: `dy_out = dx * y / (x + dx)`
    (Solidity: the `if` branch where `token0 == tokenIn`) -/
def amountOutX (p : Pool) (dx : ℚ) : ℚ :=
  dx * p.y / (p.x + dx)

/-- Exact no-fee output of X when swapping `dy` units of Y into the pool.
    Formula: `dx_out = dy * x / (y + dy)`
    (Solidity: the `else` branch where `token1 == tokenIn`) -/
def amountOutY (p : Pool) (dy : ℚ) : ℚ :=
  dy * p.x / (p.y + dy)

/-! ## Swap operations

  A full swap updates both reserves atomically. In Solidity:

    // X → Y swap
    Pools[PID].amount0 += amount;                    // x' = x + dx
    Pools[PID].amount1 -= uint(amountOut);           // y' = y - dy_out

  We model the same state transition as a pure function returning a new Pool.
-/

/-- Pool state after swapping `dx` of X in.
    New reserves: `x' = x + dx`, `y' = y - amountOutX(dx)`.
    (Solidity: the `if(token0 == tokenIn)` branch of `swap`) -/
def swapX (p : Pool) (dx : ℚ) : Pool :=
  { x := p.x + dx
    y := p.y - amountOutX p dx }

/-- Pool state after swapping `dy` of Y in.
    New reserves: `x' = x - amountOutY(dy)`, `y' = y + dy`.
    (Solidity: the `else` branch of `swap`) -/
def swapY (p : Pool) (dy : ℚ) : Pool :=
  { x := p.x - amountOutY p dy
    y := p.y + dy }

/-! ## Auxiliary operations -/

/-- Arbitrary reserve mutation — adds to both reserves.
    This is NOT proper LP-share accounting (no mint/burn of LP tokens);
    it corresponds loosely to the Solidity `deposit` function:

      Pools[PID].amount0 += amount_token0;
      Pools[PID].amount1 += amount_token1;
-/
def deposit (p : Pool) (dx dy : ℚ) : Pool :=
  { x := p.x + dx
    y := p.y + dy }

/-! ## Total Value Locked (TVL)

  In the Solidity contract:

    function totalValueLocked(uint PID, address token0) public view returns (int rate, int tvl) {
      rate = amountX.div(amountY);
      tvl  = rate * amountY + amountX;   // = 2 * amountX for a balanced pool
    }

  For a constant-product pool the spot-price TVL always simplifies to `2x`
  (denominated in X) or `2y` (denominated in Y). We prove this identity
  formally in `Theorems.lean` (`valueInX_eq_two_x`, `valueInY_eq_two_y`).
-/

/-- Pool value at spot price, denominated in X.
    For a valid pool: `valueInX p = 2 * p.x`. -/
def valueInX (p : Pool) : ℚ :=
  p.x + rateXperY p * p.y

/-- Pool value at spot price, denominated in Y.
    For a valid pool: `valueInY p = 2 * p.y`. -/
def valueInY (p : Pool) : ℚ :=
  p.y + rateYperX p * p.x

end AMM
