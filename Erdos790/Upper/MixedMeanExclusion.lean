import Erdos790.Upper.MixedMeanResidual
import Erdos790.Upper.ResidualRelations

/-!
# Excluding a selected head that is an earlier mixed dyadic mean
-/

namespace Erdos790.Upper

theorem selected_head_not_dyadic_mean
    {d earlier start j delay width Q U constant head a K threshold : ℕ}
    (amplification : ℕ) (H : Fin d) (S : ℕ → Finset ℤ)
    (word : ℕ → ℤ → Fin d → Fin 2) (C B : Finset ℕ)
    (hwidth : 0 < width) (hQ : 0 < Q) (hbase : earlier ≤ start)
    (hamp : amplification = 2 ^ (delay + 3)) (hj : j < start + delay)
    (hdelay : delay ≤ 5 * width)
    (hD : (amplification : ℤ) * AuxiliaryParameters.timeCount d + 1 ≤ (2 : ℤ) ^ width - 1)
    (halign : 2 * 2 ^ (d + H.val) ∣ a)
    (hindexLower : d * width + 2 * width ≤ j - earlier + width * H.val)
    (hindexUpper : j - earlier + width * H.val < d * width + 4 * width)
    (hS : ∀ k, ∀ t ∈ S k, start ≤ k ∧ (a : ℤ) ≤ t ∧ t < (a : ℤ) + 2 * 2 ^ (d + H.val))
    (hword : ∀ k, ∀ t ∈ S k, ∀ h : Fin d, H < h → word k t h = word j head h)
    (hselected : ∀ k, ∀ t ∈ S k,
      2 ^ k * nativeTentValue amplification (2 ^ width) constant Q U t.toNat (word k t) ∈ B)
    (hhead : (head : ℤ) ∈ S j)
    (hC : ∀ u ∈ C, Q * (2 ^ width) ^ d ≤ u ∧ u < 2 * (Q * (2 ^ width) ^ d))
    (hcover : SumCover C K threshold) (hheavy : K ≤ (levelSlice earlier C B).card)
    (hthreshold : threshold ≤ (2 ^ width) ^ 2 * (Q * (2 ^ width) ^ d))
    (hB : RepeatedSumFree ((2 ^ width) ^ 6) B) :
    ¬ DyadicMean S ((a : ℤ) + 2 ^ (d + H.val)) j head := by
  intro hmean
  obtain ⟨near, residual, hnear, hlength, hrelation, hlower, hupper⟩ :=
    dyadic_mean_residual amplification H S word B hwidth hQ hbase hamp hj hD halign
      hindexLower hindexUpper hS hword hselected hhead hmean
  have hq : 2 ≤ 2 ^ width := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) hwidth
  have htwo : 2 ≤ (2 ^ width) ^ 2 := by nlinarith
  have hheadB : 2 ^ j * nativeTentValue amplification (2 ^ width) constant Q U head (word j head) ∈ B := by
    simpa only [Int.toNat_natCast] using hselected j head hhead
  apply heavy_residual_impossible (C := C) (B := B) (i := earlier)
    (X := Q * (2 ^ width) ^ d) (r := (2 ^ width) ^ 5)
    (by positivity) hC hcover hheavy hB hheadB near hnear
    (hthreshold.trans hlower) ((Nat.mul_le_mul_right _ htwo).trans hlower) hupper
    ((Nat.add_le_add_right hlength _).trans (dyadic_arity_budget hwidth hdelay)) hrelation

end Erdos790.Upper
