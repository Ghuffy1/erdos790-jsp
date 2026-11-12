import Erdos790.Upper.ClusterRecurrence
import Erdos790.Upper.SeedParameters

/-!
# The numerical recurrence for the recursive cell partition
-/

namespace Erdos790.Upper

theorem clusterDensity_antitone : Antitone clusterDensity := by
  intro a b hab
  unfold clusterDensity
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have habReal : (a : ℝ) ≤ b := by exact_mod_cast hab
  linarith

theorem cluster_budget_step (s : ℕ) :
    (2 : ℝ) ^ s * clusterSequence 1200 s +
      ((2 : ℝ) ^ (s + 1) * clusterDensity (s + 1) +
        600 * (s + 2 : ℝ) ^ 2) / 2 ≤
      (2 : ℝ) ^ (s + 1) * clusterSequence 1200 (s + 1) := by
  have hη : clusterDensity (s + 1) ≤ clusterDensity s :=
    clusterDensity_antitone (by omega)
  have hηScaled := mul_le_mul_of_nonneg_left hη (by positivity : 0 ≤ (2 : ℝ) ^ s)
  have hpoly : 300 * (s + 2 : ℝ) ^ 2 ≤ 1200 * (s + 1 : ℝ) ^ 2 := by
    have := Nat.cast_nonneg (α := ℝ) s
    nlinarith [sq_nonneg (s : ℝ)]
  have hpow : (2 : ℝ) ^ (s + 1) * (1 / 2 : ℝ) ^ (s + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hsequence : clusterSequence 1200 (s + 1) =
      clusterSequence 1200 s / 2 + clusterDensity s / 2 +
        1200 * ((s + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (s + 1) := by
    rw [clusterSequence]
    change clusterSequence 1200 s / 2 +
        (clusterDensity s / 2 +
          1200 * ((s + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (s + 1)) = _
    ring
  have hpowSucc : (2 : ℝ) ^ (s + 1) = (2 : ℝ) ^ s * 2 := by rw [pow_succ]
  have hidentity : (2 : ℝ) ^ (s + 1) *
        (clusterSequence 1200 s / 2 + clusterDensity s / 2 +
          1200 * ((s + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (s + 1)) =
      (2 : ℝ) ^ s * clusterSequence 1200 s +
        (2 : ℝ) ^ s * clusterDensity s + 1200 * (s + 1 : ℝ) ^ 2 := by
    push_cast
    calc
      _ = (2 : ℝ) ^ (s + 1) * clusterSequence 1200 s / 2 +
          (2 : ℝ) ^ (s + 1) * clusterDensity s / 2 +
          1200 * (s + 1 : ℝ) ^ 2 *
            ((2 : ℝ) ^ (s + 1) * (1 / 2 : ℝ) ^ (s + 1)) := by ring
      _ = _ := by rw [hpow, hpowSucc]; ring
  rw [hsequence, hidentity, hpowSucc]
  nlinarith

theorem cluster_budget_step_scaled {s : ℕ} {volume children removed : ℝ}
    (hvolume : 0 ≤ volume)
    (hchildren : children ≤ (2 : ℝ) ^ s * clusterSequence 1200 s * volume)
    (hremoved : removed ≤
      ((2 : ℝ) ^ (s + 1) * clusterDensity (s + 1) +
        600 * (s + 2 : ℝ) ^ 2) * (volume / 2)) :
    children + removed ≤ (2 : ℝ) ^ (s + 1) *
      clusterSequence 1200 (s + 1) * volume := by
  have hstep := mul_le_mul_of_nonneg_right (cluster_budget_step s) hvolume
  nlinarith

end Erdos790.Upper
