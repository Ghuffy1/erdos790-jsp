import Erdos790.Upper.CyclicPhaseCount
import Erdos790.Upper.GeometricCharacters

/-!
# Cyclic distance gives a lower bound for a character chord
-/

namespace Erdos790.Upper

theorem sin_phase_lower {r : ℝ} (hr0 : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    2 * r ≤ Real.sin (Real.pi * r) := by
  have hπ := Real.pi_pos
  have h := Real.mul_le_sin (mul_nonneg hπ.le hr0)
    (show Real.pi * r ≤ Real.pi / 2 by nlinarith)
  have hfactor : 2 / Real.pi * (Real.pi * r) = 2 * r := by field_simp
  rwa [hfactor] at h

theorem phase_chord_lower_unit_interval {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    4 * min r (1 - r) ≤
      ‖Complex.exp (Complex.I * (2 * Real.pi * r : ℝ)) - 1‖ := by
  have hsin : 2 * min r (1 - r) ≤ Real.sin (Real.pi * r) := by
    by_cases hhalf : r ≤ 1 / 2
    · rw [min_eq_left (by linarith)]
      exact sin_phase_lower hr0 hhalf
    · have h := sin_phase_lower (r := 1 - r) (by linarith) (by linarith)
      rw [show Real.pi * (1 - r) = Real.pi - Real.pi * r by ring,
        Real.sin_pi_sub] at h
      rwa [min_eq_right (by linarith)]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * r / 2 = Real.pi * r by ring,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [le_abs_self (Real.sin (Real.pi * r))]

theorem stdAddChar_chord_lower {p : ℕ} [NeZero p] (a : ZMod p) :
    4 * min ((a.val : ℝ) / p) (1 - (a.val : ℝ) / p) ≤
      ‖1 - ZMod.stdAddChar a‖ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have haval : (a.val : ℝ) < p := by exact_mod_cast ZMod.val_lt a
  have h0 : (0 : ℝ) ≤ (a.val : ℝ) / p := by positivity
  have h1 : (a.val : ℝ) / p ≤ 1 := (div_le_one hp).mpr haval.le
  have hchar : ZMod.stdAddChar a =
      Complex.exp (Complex.I * (2 * Real.pi * ((a.val : ℝ) / p) : ℝ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    push_cast
    ring
  rw [hchar, norm_sub_rev]
  exact phase_chord_lower_unit_interval h0 h1

theorem not_nearZero_chord_lower {p p0 : ℕ} [NeZero p] (hp0 : 0 < p0)
    (a : ZMod p) (hnot : a ∉ nearZeroResidues p (p / p0 + 1)) :
    4 / (p0 : ℝ) ≤ ‖1 - ZMod.stdAddChar a‖ := by
  have hmin : p / p0 + 1 ≤ min a.val (p - a.val) := by
    have h := hnot
    simp only [nearZeroResidues, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at h
    exact h
  have hleftNat : p / p0 + 1 ≤ a.val := hmin.trans (min_le_left _ _)
  have hrightNat : p / p0 + 1 ≤ p - a.val := hmin.trans (min_le_right _ _)
  have hdivision : p < (p / p0 + 1) * p0 := by
    have hmod := Nat.mod_lt p hp0
    have hdecomp := Nat.mod_add_div p p0
    nlinarith
  have hleftCross : p ≤ a.val * p0 :=
    hdivision.le.trans (Nat.mul_le_mul_right p0 hleftNat)
  have hrightCross : p ≤ (p - a.val) * p0 :=
    hdivision.le.trans (Nat.mul_le_mul_right p0 hrightNat)
  have hpReal : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hp0Real : (0 : ℝ) < p0 := by exact_mod_cast hp0
  have hleft : (1 : ℝ) / p0 ≤ (a.val : ℝ) / p := by
    apply (div_le_div_iff₀ hp0Real hpReal).mpr
    simp only [one_mul]
    exact_mod_cast hleftCross
  have hright : (1 : ℝ) / p0 ≤ 1 - (a.val : ℝ) / p := by
    have hratio : 1 - (a.val : ℝ) / p = ((p - a.val : ℕ) : ℝ) / p := by
      rw [Nat.cast_sub (ZMod.val_lt a).le]
      field_simp
    rw [hratio]
    apply (div_le_div_iff₀ hp0Real hpReal).mpr
    simp only [one_mul]
    exact_mod_cast hrightCross
  calc
    4 / (p0 : ℝ) = 4 * ((1 : ℝ) / p0) := by ring
    _ ≤ 4 * min ((a.val : ℝ) / p) (1 - (a.val : ℝ) / p) :=
      mul_le_mul_of_nonneg_left (le_min hleft hright) (by norm_num)
    _ ≤ ‖1 - ZMod.stdAddChar a‖ := stdAddChar_chord_lower a

end Erdos790.Upper
