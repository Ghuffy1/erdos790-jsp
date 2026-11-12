import Erdos790.Upper.ProgressionInput
import Erdos790.Upper.IntervalLift
import Erdos790.Upper.EventualCoarse
import Erdos790.Upper.AsymptoticPacking
import Erdos790.Upper.Conclusion

/-!
# The complete construction from the quantitative progression theorem
-/

open Filter

namespace Erdos790.Upper

open AuxiliaryParameters

theorem eventual_upper_from_quantitative
    (hquantitative : OAI.Erdos3.QuantitativeDensityBound 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, (Erdos790.l n : ℝ) ≤ C * n / Real.log n ^ 2 := by
  apply eventual_upper_of_exponential_witnesses
    (B := coarseConstant + 2) (K := 105) (by have h := coarseConstant_pos; linarith) (by decide)
  have hsample := eventually_polynomial_le_power (700000 ^ 4) 8 2 (by decide)
  have hlevels := eventually_polynomial_le_power 7 2 2 (by decide)
  filter_upwards [eventual_coarse_host, eventual_center_rich_from_quantitative hquantitative,
    hsample, hlevels, eventually_ge_atTop 1] with d hcoarse hcenters hsample hlevels hd
  obtain ⟨F, hFcard, hFpositive, hFbound⟩ := hcoarse
  obtain ⟨A, bound, hApositive, hAcard, hAbound, hscaled⟩ := interval_lift_witness
    (levelCount_pos d) (coarseSize_pos d) (liftIntervalLength_pos d)
    hFcard hFpositive hcenters hFbound
  have hsampleBound : sampleSize d ≤ 2 ^ d := by
    calc
      _ ≤ roughScale d ^ 4 := sampleSize_le_fourth_power d
      _ ≤ (700000 * (d + 1) ^ 2) ^ 4 := Nat.pow_le_pow_left (roughScale_le_quadratic d) 4
      _ = (700000 ^ 4) * (d + 1) ^ 8 := by ring
      _ ≤ 2 ^ d := hsample
  have hlevelBound : levelCount d ≤ 2 ^ d := by
    have hpoly : levelCount d ≤ 7 * (d + 1) ^ 2 := by unfold levelCount; nlinarith
    exact hpoly.trans hlevels
  have hcoarseSize : coarseSize d ≤ 2 ^ (4 * d) := by
    calc
      _ ≤ 2 ^ d * 2 ^ (3 * d) := Nat.mul_le_mul_right _ hsampleBound
      _ = 2 ^ (4 * d) := by rw [← pow_add]; congr 1; omega
  have hAsize : A.card ≤ 2 ^ (105 * d) := by
    rw [hAcard]
    calc
      _ ≤ liftIntervalLength d * 2 ^ d * 2 ^ (4 * d) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hlevelBound) hcoarseSize
      _ = 2 ^ (105 * d) := by
        unfold liftIntervalLength
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  have hApos : 0 < A.card := by
    rw [hAcard]
    exact Nat.mul_pos (Nat.mul_pos (liftIntervalLength_pos d) (levelCount_pos d)) (coarseSize_pos d)
  have hlevelLower : (d + 1) ^ 2 ≤ levelCount d := by unfold levelCount; nlinarith
  have hlevelReal : ((d : ℝ) + 1) ^ 2 ≤ levelCount d := by exact_mod_cast hlevelLower
  refine ⟨A, bound, hApositive, hApos, hAbound, hAsize, ?_⟩
  exact (mul_le_mul_of_nonneg_left hlevelReal (Nat.cast_nonneg bound)).trans hscaled

theorem matchingOrder_from_quantitative
    (hquantitative : OAI.Erdos3.QuantitativeDensityBound 3) : Erdos790.MatchingOrder :=
  Erdos790.matchingOrder_of_eventual_upper (eventual_upper_from_quantitative hquantitative)

end Erdos790.Upper
