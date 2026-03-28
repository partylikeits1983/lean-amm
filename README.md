# lean-amm — Formally Verified Constant-Product AMM

A Lean 4 + Mathlib project that formally verifies the core mathematics of a constant-product automated market maker (AMM), using exact rational arithmetic (`ℚ`).

## What this proves

This project models a Uniswap-style `x * y = k` pool and proves **12 theorems** about its behavior:

| # | Theorem | Statement |
|---|---------|-----------|
| 1 | `k_swapX_eq` | Swapping X preserves the invariant `k = x * y` |
| 2 | `k_swapY_eq` | Swapping Y preserves the invariant (symmetric) |
| 3 | `swapX_y_closed_form` | Post-swap Y reserve = `x * y / (x + dx)` |
| 4 | `swapY_x_closed_form` | Post-swap X reserve = `y * x / (y + dy)` |
| 5 | `output_nonneg_swapX` | Output ≥ 0 for valid pool and nonneg input |
| 6 | `output_nonneg_swapY` | Symmetric nonnegativity |
| 7 | `output_lt_reserve_swapX` | Output < reserve (can't drain the pool) |
| 8 | `output_lt_reserve_swapY` | Symmetric bound |
| 9 | `valid_swapX` | Valid pool stays valid after swap |
| 10 | `valid_swapY` | Symmetric validity preservation |
| 11 | `monotone_amountOutX` | More input → more output |
| 12 | `monotone_amountOutY` | Symmetric monotonicity |
| 13 | `rateYperX_decreases_after_swapX` | Swapping X in decreases Y-per-X rate |
| 14 | `rateXperY_decreases_after_swapY` | Swapping Y in decreases X-per-Y rate |
| 15 | `valueInX_eq_two_x` | TVL in X at spot = `2 * x` |
| 16 | `valueInY_eq_two_y` | TVL in Y at spot = `2 * y` |

All proofs use trusted tactics (`ring`, `field_simp`, `positivity`, `linarith`, `nlinarith`, `simp`). No `native_decide`, no `sorry`.

## What this does NOT model

- No ERC20 transfers, addresses, or blockchain plumbing
- No LP share accounting (deposit/withdraw with proportional minting)
- No fees
- No integer/fixed-point arithmetic (exact rationals only)
- No multi-hop routing

These are intentional scope limits for this educational version. 

## Core definitions

```lean
structure Pool where
  x : ℚ    -- reserve of token X
  y : ℚ    -- reserve of token Y

def Valid (p : Pool) : Prop := 0 < p.x ∧ 0 < p.y
def k (p : Pool) : ℚ := p.x * p.y

-- Swap dx of X into the pool, receive Y
def amountOutX (p : Pool) (dx : ℚ) : ℚ := dx * p.y / (p.x + dx)

-- New pool state after swap
def swapX (p : Pool) (dx : ℚ) : Pool :=
  { x := p.x + dx, y := p.y - amountOutX p dx }
```

## Prerequisites

- [Lean 4](https://lean-lang.org/) via [elan](https://github.com/leanprover/elan)
- Internet connection (to fetch Mathlib)

## Building

```bash
# First time: fetch dependencies and prebuilt Mathlib cache
lake update

# Build everything
lake build

# Build tests
lake build AmmTest
```

The first `lake update` downloads ~500MB of Lean toolchain and ~8000 prebuilt Mathlib `.olean` files. Subsequent builds only compile the project's own files (~30 seconds).

## Example output

From `#eval` in the test file, with pool `(x=5, y=10)`:

```
amountOutX p0 1  = 5/3      -- swap 1 X → get 1.67 Y
amountOutX p0 2  = 20/7     -- swap 2 X → get 2.86 Y (diminishing returns)
amountOutX p0 5  = 5        -- swap 5 X → get 5 Y
k p0             = 50       -- invariant
k (swapX p0 1)   = 50       -- invariant preserved!
rateYperX p0     = 2        -- spot price before
rateYperX (swapX p0 1) = 25/18  -- spot price after (decreased)
valueInX p0      = 10       -- = 2 * x
valueInY p0      = 20       -- = 2 * y
```

## Tactic reference

The proofs use these Lean 4 / Mathlib tactics:

| Tactic | Used for |
|--------|----------|
| `ring` | Polynomial identities after clearing denominators |
| `field_simp` | Clearing denominators in rational expressions |
| `linarith` | Linear arithmetic over ordered fields |
| `nlinarith` | Nonlinear arithmetic (products of inequalities) |
| `positivity` | Proving expressions are positive/nonneg |
| `simp` | Simplification with definitional unfolding |
| `norm_num` | Numeric computation in tests |

## License

MIT
