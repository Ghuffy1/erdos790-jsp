import Erdos790.Upper.SeedParameters
import Erdos790.Upper.LatticeRefinement

/-!
# Quantitative room and span invariants for repeated lattice refinement
-/

namespace Erdos790.Upper

theorem refinement_core_room {η E M g : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hg : η * g ≤ 2)
    (hspan : η ^ 3 * M / 32 ≤ E) (hlarge : 1024 ≤ η ^ 4 * M) : 8 * g + 8 ≤ E := by
  have hscaled := mul_le_mul_of_nonneg_left hspan hη.le
  have hbound : η * (8 * g + 8) ≤ η * E := by nlinarith
  exact (mul_le_mul_iff_of_pos_left hη).mp hbound

theorem refinement_scale_room {η E M g B : ℝ}
    (hη : 0 < η) (hM : 0 ≤ M) (hB : 0 ≤ B) (hg : η * g ≤ 2)
    (hspan : η ^ 3 * M / 32 ≤ E) (hbudget : 512 ≤ η ^ 4 * B) : 8 * g * M ≤ B * E := by
  have hspanMul := mul_le_mul_of_nonneg_left hspan (mul_nonneg hη.le hB)
  have hbudgetMul := mul_le_mul_of_nonneg_right hbudget hM
  have hgMul := mul_le_mul_of_nonneg_right hg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hM)
  have hscaled : η * (8 * g * M) ≤ η * (B * E) := by nlinarith
  exact (mul_le_mul_iff_of_pos_left hη).mp hscaled

theorem refinement_span_invariant {E E' E0 g g' g0 : ℝ}
    (hE0 : 0 ≤ E0) (hg' : 0 ≤ g') (hhalve : 2 * g' ≤ g)
    (hquarter : E ≤ 4 * E') (hinvariant : E0 * g ^ 2 ≤ E * g0 ^ 2) :
    E0 * g' ^ 2 ≤ E' * g0 ^ 2 := by
  have hsq : 4 * g' ^ 2 ≤ g ^ 2 := by nlinarith
  have hmod := mul_le_mul_of_nonneg_left hsq hE0
  have hspan := mul_le_mul_of_nonneg_right hquarter (sq_nonneg g0)
  nlinarith

theorem refinement_span_lower {η E E0 M g g0 : ℝ}
    (hη : 0 < η) (hE : 0 ≤ E) (hM : 0 ≤ M) (hg0 : 0 ≤ g0) (hg : 1 ≤ g)
    (hg0Bound : η * g0 ≤ 2) (hseed : η * M / 8 ≤ E0)
    (hinvariant : E0 * g ^ 2 ≤ E * g0 ^ 2) : η ^ 3 * M / 32 ≤ E := by
  have hE0 : 0 ≤ E0 := (by positivity : 0 ≤ η * M / 8).trans hseed
  have hgsq : 1 ≤ g ^ 2 := by nlinarith
  have hE0g : E0 ≤ E0 * g ^ 2 := by nlinarith
  have hbound : η ^ 2 * g0 ^ 2 ≤ 4 := by
    have hprod : 0 ≤ η * g0 := mul_nonneg hη.le hg0
    have hfactor := mul_nonneg (sub_nonneg.mpr hg0Bound)
      (by linarith : 0 ≤ 2 + η * g0)
    nlinarith
  have hboundE := mul_le_mul_of_nonneg_right hbound hE
  have hscale := mul_le_mul_of_nonneg_left (hE0g.trans hinvariant) (sq_nonneg η)
  have hseedScale := mul_le_mul_of_nonneg_left hseed (sq_nonneg η)
  nlinarith

theorem halving_sequence_bound {g : ℕ → ℕ} {r : ℕ}
    (hhalve : ∀ i < r, 2 * g (i + 1) ≤ g i) : 2 ^ r * g r ≤ g 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hprevious := ih (fun i hi => hhalve i (by omega))
    calc
      2 ^ (r + 1) * g (r + 1) = 2 ^ r * (2 * g (r + 1)) := by ring
      _ ≤ 2 ^ r * g r := Nat.mul_le_mul_left _ (hhalve r (by omega))
      _ ≤ g 0 := hprevious

theorem halving_sequence_length {g : ℕ → ℕ} {r b : ℕ}
    (hhalve : ∀ i < r, 2 * g (i + 1) ≤ g i) (hpositive : 0 < g r)
    (hbudget : g 0 < 2 ^ b) : r < b := by
  have hbound := halving_sequence_bound hhalve
  have hpower : 2 ^ r < 2 ^ b :=
    (Nat.le_mul_of_pos_right _ hpositive).trans_lt (hbound.trans_lt hbudget)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpower

theorem cluster_refinement_count {g : ℕ → ℕ} {r s : ℕ}
    (hhalve : ∀ i < r, 2 * g (i + 1) ≤ g i) (hpositive : 0 < g r)
    (hbudget : clusterDensity s * g 0 ≤ 2) : r < s + 16 := by
  have hpower : g 0 < 2 ^ (s + 16) := by
    simpa only [add_zero] using seed_power_room (g := g 0) (K := 0)
      (clusterDensity_pos s) (clusterDensity_le_one s) hbudget (by norm_num)
      (cluster_seed_delay_budget s)
  exact halving_sequence_length hhalve hpositive hpower

theorem cell_phase_charge_bound {s r : ℕ} (hr : r ≤ s + 16) :
    (s + 16) + 3 * (r + 1) + (s + 28) * r ≤ 600 * (s + 1) ^ 2 := by
  have hproduct := Nat.mul_le_mul_left (s + 28) hr
  nlinarith

end Erdos790.Upper
