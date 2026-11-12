import Erdos790.Upper.TotientDensity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Quantitative budgets for the auxiliary sample
-/

namespace Erdos790.Upper

noncomputable def phaseSampleExponent (S : ℝ) : ℕ := Nat.ceil (100 * (1 + Real.log S))

theorem phaseSampleExponent_budget {S T : ℝ} (hS : 1 ≤ S) (hT0 : 0 ≤ T) (hTS : T ≤ S) :
    T * Real.exp (-(phaseSampleExponent S : ℝ) / 2) ≤ 1 / 2 := by
  have hSpos : 0 < S := by linarith
  have hlog : 0 ≤ Real.log S := Real.log_nonneg hS
  have hlogtwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hceil : 100 * (1 + Real.log S) ≤ (phaseSampleExponent S : ℝ) :=
    Nat.le_ceil _
  have hlogprod : Real.log (2 * S) = Real.log 2 + Real.log S :=
    Real.log_mul (by norm_num) hSpos.ne'
  have hlarge : 2 * Real.log (2 * S) ≤ (phaseSampleExponent S : ℝ) := by
    rw [hlogprod]
    linarith
  have hexp : Real.exp (-(phaseSampleExponent S : ℝ) / 2) ≤ (2 * S)⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log (2 * S)) := Real.exp_le_exp.mpr (by linarith)
      _ = (2 * S)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
  calc
    T * Real.exp (-(phaseSampleExponent S : ℝ) / 2) ≤ T * (2 * S)⁻¹ :=
      mul_le_mul_of_nonneg_left hexp hT0
    _ ≤ S * (2 * S)⁻¹ := mul_le_mul_of_nonneg_right hTS (by positivity)
    _ = 1 / 2 := by field_simp

theorem phaseSampleExponent_le {S : ℝ} {B : ℕ}
    (hbound : 100 * (1 + Real.log S) ≤ B) : phaseSampleExponent S ≤ B := by
  exact Nat.ceil_le.mpr hbound

theorem factorial_square_dominates_power {v exponent : ℕ} (hv : 0 < v)
    (hexponent : exponent ≤ v ^ 2 - v) : v ^ exponent ≤ (v ^ 2).factorial := by
  have hvv : v ≤ v ^ 2 := by nlinarith
  calc
    v ^ exponent ≤ v ^ (v ^ 2 - v) := Nat.pow_le_pow_right hv hexponent
    _ ≤ v.factorial * v ^ (v ^ 2 - v) :=
      Nat.le_mul_of_pos_left _ (Nat.factorial_pos v)
    _ ≤ (v ^ 2).factorial := Nat.factorial_mul_pow_sub_le_factorial hvv

theorem factorial_square_dominates_twentieth_power {v : ℕ} (hv : 5 ≤ v) :
    v ^ 20 ≤ (v ^ 2).factorial := by
  have hvv : v ≤ v ^ 2 := by nlinarith
  have hsub : 4 ≤ v - 1 := by omega
  have hmul := Nat.mul_le_mul hv hsub
  have hexponent : 20 ≤ v ^ 2 - v := by
    have hsubidentity := Nat.sub_add_cancel (show 1 ≤ v by omega)
    have hsquare := Nat.sub_add_cancel hvv
    nlinarith
  exact factorial_square_dominates_power (by omega) hexponent

theorem factorial_residue_collision_budget {v J : ℕ} (hv : 5 ≤ v) (hJ : J ≤ v ^ 5) :
    4 * J ^ 2 ≤ (v ^ 2).factorial.totient := by
  have hfactorial := factorial_square_dominates_twentieth_power hv
  have htotient := factorial_totient_density (n := v ^ 2) (by omega : 0 < v) le_rfl
  have hJsquare := Nat.pow_le_pow_left hJ 2
  have h16 : 16 ≤ v ^ 9 := by
    have h := Nat.pow_le_pow_left (show 2 ≤ v by omega) 9
    norm_num at h
    omega
  have hlarge : 16 * v * J ^ 2 ≤ (v ^ 2).factorial := by
    calc
      16 * v * J ^ 2 ≤ 16 * v * (v ^ 5) ^ 2 := Nat.mul_le_mul_left _ hJsquare
      _ = 16 * v ^ 11 := by ring
      _ ≤ v ^ 9 * v ^ 11 := Nat.mul_le_mul_right _ h16
      _ = v ^ 20 := by rw [← pow_add]
      _ ≤ (v ^ 2).factorial := hfactorial
  have hcancel : (4 * v) * (4 * J ^ 2) ≤ (4 * v) * (v ^ 2).factorial.totient := by
    calc
      _ = 16 * v * J ^ 2 := by ring
      _ ≤ (v ^ 2).factorial := hlarge
      _ ≤ _ := htotient
  exact Nat.le_of_mul_le_mul_left hcancel (by omega)

end Erdos790.Upper
