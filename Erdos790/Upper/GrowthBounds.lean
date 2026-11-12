import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Eventual exponential domination with natural-number parameters
-/

open Filter Asymptotics

namespace Erdos790.Upper

theorem eventually_polynomial_le_power (C k b : ℕ) (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, C * (n + 1) ^ k ≤ b ^ n := by
  let A : ℝ := C * 2 ^ k
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpositive : 0 < (A + 1)⁻¹ := by positivity
  have hsmall : (fun n : ℕ => (n : ℝ) ^ k) =o[atTop] fun n => (b : ℝ) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k (by exact_mod_cast hb)
  filter_upwards [hsmall.bound hpositive, eventually_ge_atTop 1] with n hn hn1
  have hbound : (n : ℝ) ^ k ≤ (A + 1)⁻¹ * (b : ℝ) ^ n := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ k),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b : ℝ) ^ n)] using hn
  have hproduct : (A + 1) * (n : ℝ) ^ k ≤ (b : ℝ) ^ n := by
    calc
      _ ≤ (A + 1) * ((A + 1)⁻¹ * (b : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = (b : ℝ) ^ n := by rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hshift : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hpower := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) hshift k
  have hfinal : (C : ℝ) * ((n + 1 : ℕ) : ℝ) ^ k ≤ (b : ℝ) ^ n := by
    calc
      _ ≤ (C : ℝ) * (2 * (n : ℝ)) ^ k := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = A * (n : ℝ) ^ k := by dsimp [A]; rw [mul_pow]; ring
      _ ≤ (A + 1) * (n : ℝ) ^ k := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (b : ℝ) ^ n := hproduct
  exact_mod_cast hfinal

theorem eventually_polynomial_le_power_div (C k b q : ℕ) (hb : 1 < b) (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, C * (n + 1) ^ k ≤ b ^ (n / q) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_polynomial_le_power (C * q ^ k) k b hb)
  apply eventually_atTop.mpr
  refine ⟨q * N, ?_⟩
  intro n hn
  have hquot : N ≤ n / q := (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using hn)
  have hshift : n + 1 ≤ q * (n / q + 1) := by
    have hmod := Nat.mod_lt n hq
    have hdecomp := Nat.mod_add_div n q
    nlinarith
  calc
    C * (n + 1) ^ k ≤ C * (q * (n / q + 1)) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hshift k)
    _ = (C * q ^ k) * (n / q + 1) ^ k := by rw [mul_pow]; ring
    _ ≤ b ^ (n / q) := hN _ hquot

end Erdos790.Upper
