import Erdos790.Upper.TentParameters
import Erdos790.Upper.RepeatedLists

/-!
# Forbidden gaps and repeated base points in dyadic levels
-/

namespace Erdos790.Upper

theorem SumCover.threshold_mono {C : Finset ℕ} {K a b : ℕ}
    (h : SumCover C K a) (hab : a ≤ b) : SumCover C K b := by
  intro S hS hcard N hN
  exact h S hS hcard N (hab.trans hN)

theorem RepeatedSumFree.no_dyadic_repeat {R i j u : ℕ} {B : Finset ℕ}
    (hB : RepeatedSumFree R B) (hi : 2 ^ i * u ∈ B) (hj : 2 ^ j * u ∈ B)
    (hij : i < j) (hR : 2 ^ (j - i) ≤ R) : False := by
  have htwo : 2 ≤ 2 ^ (j - i) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j - i) := Nat.pow_le_pow_right (by decide) (by omega)
  have hmem : ∀ x ∈ List.replicate (2 ^ (j - i)) (2 ^ i * u), x ∈ B := by
    intro x hx
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hx
    exact hi
  apply hB.not_list_sum hj (List.replicate (2 ^ (j - i)) (2 ^ i * u))
    hmem (by simpa using htwo) (by simpa using hR)
  simp only [List.sum_replicate, nsmul_eq_mul, Nat.cast_id]
  rw [← Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hij.le]

namespace AuxiliaryParameters

def arityLimit (d : ℕ) : ℕ := 2 ^ (36 * d)

theorem gapScale_two_le (d : ℕ) : 2 ≤ gapScale d := by
  have hsample : 0 < sampleSize d :=
    Nat.mul_pos (Nat.mul_pos (by decide) (levelCount_pos d)) (sampleExponent_pos d)
  have hcoefficient : 0 < coefficientRange d := by
    unfold coefficientRange
    exact Nat.mul_pos (by decide) (Nat.pow_pos (by have h := roughScale_large d; omega))
  have hproduct := Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hsample) hcoefficient
  unfold gapScale
  omega

theorem occupied_level_gap_impossible {d K i j : ℕ} {C B : Finset ℕ}
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d))
    (hB : RepeatedSumFree (arityLimit d) B)
    (hheavy : K ≤ (levelSlice i C B).card)
    (hoccupied : (levelSlice j C B).Nonempty)
    (hij : i < j) (hlower : clusterWidth d ≤ j - i)
    (hupper : j - i + 1 ≤ 36 * d) : False := by
  have hthreshold : sumThreshold d ≤ gapScale d * baseRange d := by
    unfold sumThreshold gapScale
    exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hgap : gapScale d ≤ 2 ^ (j - i) :=
    (gapScale_lt_power d).le.trans (Nat.pow_le_pow_right (by decide) hlower)
  exact heavy_level_gap_impossible (baseRange_pos d) hC hB
    (hcover.threshold_mono hthreshold) hheavy hoccupied hij (gapScale_two_le d) hgap
    (Nat.pow_le_pow_right (by decide) hupper)

end AuxiliaryParameters
end Erdos790.Upper
