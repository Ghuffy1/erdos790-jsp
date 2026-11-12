import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Converting the quantitative progression bound to inverse polynomial density
-/

open Filter

namespace Erdos790.Upper

theorem quantitative_density_polynomial_decay (E : ℕ → ℕ)
    {C c η : ℝ} (hC : 0 < C) (hc : 0 < c) (hη : 0 < η)
    (hE : ∀ N : ℕ, 3 ≤ N → (E N : ℝ) ≤
      C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)))
    (A : ℝ) (hA : 0 < A) (p : ℕ) :
    ∀ᶠ d : ℕ in atTop,
      A * ((d : ℝ) + 1) ^ p * E (2 ^ d) ≤ (2 : ℝ) ^ d := by
  let x := fun d : ℕ => Real.log (Real.log ((2 : ℝ) ^ d))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : Tendsto x atTop atTop := by
    have hlinear : Tendsto (fun d : ℕ => (d : ℝ) * Real.log 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hlog2
    simpa only [x, Real.log_pow, Function.comp_def] using Real.tendsto_log_atTop.comp hlinear
  have hxpower := (tendsto_rpow_atTop hη).comp hx
  filter_upwards [hx.eventually_ge_atTop 1,
    hx.eventually_ge_atTop (Real.log A + Real.log C),
    hx.eventually_ge_atTop (Real.log 2 - Real.log (Real.log 2)),
    hxpower.eventually_ge_atTop ((2 * (p : ℝ) + 1) / c),
    eventually_ge_atTop 2] with d hx1 hxconst hxshift hxlarge hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hxpos : 0 < x d := by linarith
  have hxformula : x d = Real.log (d : ℝ) + Real.log (Real.log 2) := by
    dsimp [x]
    rw [Real.log_pow, Real.log_mul hdpos.ne' hlog2.ne']
  have hdplus : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hlogshift : Real.log ((d : ℝ) + 1) ≤ 2 * x d := by
    have hmono : Real.log ((d : ℝ) + 1) ≤ Real.log (2 * (d : ℝ)) :=
      Real.log_le_log hdplus (by exact_mod_cast (show d + 1 ≤ 2 * d by omega))
    rw [Real.log_mul (by norm_num) hdpos.ne'] at hmono
    linarith
  have hexponent : Real.log A + (p : ℝ) * Real.log ((d : ℝ) + 1) + Real.log C ≤
      c * (x d) ^ (1 + η) := by
    change (2 * (p : ℝ) + 1) / c ≤ (x d) ^ η at hxlarge
    have hlarge : 2 * (p : ℝ) + 1 ≤ c * (x d) ^ η := by
      have h := (div_le_iff₀ hc).mp hxlarge
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hlarge hxpos.le
    have hlogs := mul_le_mul_of_nonneg_left hlogshift (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
    rw [Real.rpow_add hxpos, Real.rpow_one]
    nlinarith
  let P := A * ((d : ℝ) + 1) ^ p * C
  have hP : 0 < P := by dsimp [P]; positivity
  have hlogP : Real.log P =
      Real.log A + (p : ℝ) * Real.log ((d : ℝ) + 1) + Real.log C := by
    dsimp [P]
    rw [Real.log_mul (mul_pos hA (pow_pos hdplus p)).ne' hC.ne',
      Real.log_mul hA.ne' (pow_pos hdplus p).ne', Real.log_pow]
  have hsmall : P * Real.exp (-c * (x d) ^ (1 + η)) ≤ 1 := by
    calc
      _ = Real.exp (Real.log P + (-c * (x d) ^ (1 + η))) := by
        rw [Real.exp_add, Real.exp_log hP]
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by rw [hlogP]; linarith)
  have hN : 3 ≤ 2 ^ d := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    norm_num at h
    omega
  have hbound := hE (2 ^ d) hN
  push_cast at hbound
  change (E (2 ^ d) : ℝ) ≤ C * (2 : ℝ) ^ d *
    Real.exp (-c * (x d) ^ (1 + η)) at hbound
  calc
    A * ((d : ℝ) + 1) ^ p * E (2 ^ d) ≤
        A * ((d : ℝ) + 1) ^ p *
          (C * (2 : ℝ) ^ d * Real.exp (-c * (x d) ^ (1 + η))) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (2 : ℝ) ^ d * (P * Real.exp (-c * (x d) ^ (1 + η))) := by dsimp [P]; ring
    _ ≤ (2 : ℝ) ^ d := mul_le_of_le_one_right (by positivity) hsmall

end Erdos790.Upper
