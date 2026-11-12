import Erdos790.Upper.FourierProducts
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Geometric character sums away from the trivial phase
-/

open Finset

namespace Erdos790.Upper

theorem geometric_norm_mul_le_two {z : ℂ} (hz : ‖z‖ ≤ 1) (B : ℕ) :
    ‖∑ i ∈ Finset.range B, z ^ i‖ * ‖1 - z‖ ≤ 2 := by
  have hpow : ‖z ^ B‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz
  calc
    ‖∑ i ∈ Finset.range B, z ^ i‖ * ‖1 - z‖ =
        ‖(∑ i ∈ Finset.range B, z ^ i) * (1 - z)‖ := (norm_mul _ _).symm
    _ = ‖1 - z ^ B‖ := by rw [geom_sum_mul_neg]
    _ ≤ ‖(1 : ℂ)‖ + ‖z ^ B‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

theorem character_factor_geometric {M B : ℕ} [NeZero M] (a : ZMod M) :
    (∑ c : Fin B, ZMod.stdAddChar (-((c.val : ZMod M) * a))) =
      ∑ i ∈ Finset.range B, (ZMod.stdAddChar (-a)) ^ i := by
  have hpow (i : ℕ) : ZMod.stdAddChar (-((i : ZMod M) * a)) =
      (ZMod.stdAddChar (-a)) ^ i := by
    rw [show -((i : ZMod M) * a) = i • (-a) by simp [nsmul_eq_mul]]
    exact AddChar.map_nsmul_eq_pow _ _ _
  simp only [hpow]
  exact Fin.sum_univ_eq_sum_range (fun i => (ZMod.stdAddChar (-a)) ^ i) B

theorem character_factor_bound_of_chord {M B : ℕ} [NeZero M] {p : ℝ}
    (a : ZMod M) (hp : 0 < p) (hB : 100 * p ≤ B)
    (hchord : 4 / p ≤ ‖1 - ZMod.stdAddChar (-a)‖) :
    ‖∑ c : Fin B, ZMod.stdAddChar (-((c.val : ZMod M) * a))‖ ≤ (B : ℝ) / 200 := by
  rw [character_factor_geometric]
  let size := ‖∑ i ∈ Finset.range B, (ZMod.stdAddChar (-a)) ^ i‖
  have hsize0 : 0 ≤ size := norm_nonneg _
  have hgeom := geometric_norm_mul_le_two
    (z := ZMod.stdAddChar (-a)) (by simp) B
  have hproduct : size * (4 / p) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hchord hsize0).trans hgeom
  have hscaled : size * 4 ≤ 2 * p := by
    calc
      size * 4 = (size * (4 / p)) * p := by field_simp
      _ ≤ 2 * p := mul_le_mul_of_nonneg_right hproduct hp.le
  change size ≤ (B : ℝ) / 200
  nlinarith

theorem phase_chord_lower {r : ℝ} (hr : |r| ≤ 1 / 2) :
    4 * |r| ≤ ‖Complex.exp (Complex.I * (2 * Real.pi * r : ℝ)) - 1‖ := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hrπ : |Real.pi * r| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hπ]
    nlinarith
  have hsin := Real.mul_abs_le_abs_sin hrπ
  have hlinear : 2 * |r| ≤ |Real.sin (Real.pi * r)| := by
    calc
      2 * |r| = 2 / Real.pi * |Real.pi * r| := by
        rw [abs_mul, abs_of_pos hπ]
        field_simp
      _ ≤ |Real.sin (Real.pi * r)| := hsin
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : 2 * Real.pi * r / 2 = Real.pi * r := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

end Erdos790.Upper
