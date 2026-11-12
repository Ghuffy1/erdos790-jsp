import Erdos790.Upper.CoordinateFamilies
import Erdos790.Upper.MixedMeanExclusion

/-!
# Mixed-mean exclusion for selected coordinate families
-/

namespace Erdos790.Upper

theorem selectedCoordinates_not_dyadic_mean
    {d earlier start j delay width Q U constant head a K threshold : ℕ}
    (amplification : ℕ) (H : Fin d)
    (family : ℕ → Finset (ℤ × (Fin d → Fin 2))) (fixed : Fin d → Fin 2)
    (C B : Finset ℕ) (hwidth : 0 < width) (hQ : 0 < Q) (hbase : earlier ≤ start)
    (hamp : amplification = 2 ^ (delay + 3)) (hj : j < start + delay)
    (hdelay : delay ≤ 5 * width)
    (hD : (amplification : ℤ) * AuxiliaryParameters.timeCount d + 1 ≤ (2 : ℤ) ^ width - 1)
    (halign : 2 * 2 ^ (d + H.val) ∣ a)
    (hindexLower : d * width + 2 * width ≤ j - earlier + width * H.val)
    (hindexUpper : j - earlier + width * H.val < d * width + 4 * width)
    (hframe : ∀ k t word, (t, word) ∈ family k →
      start ≤ k ∧ (a : ℤ) ≤ t ∧ t < (a : ℤ) + 2 * 2 ^ (d + H.val))
    (hfixed : ∀ k t word, (t, word) ∈ family k →
      ∀ h : Fin d, H < h → word h = fixed h)
    (hselected : ∀ k t word, (t, word) ∈ family k →
      2 ^ k * nativeTentValue amplification (2 ^ width) constant Q U t.toNat word ∈ B)
    (hhead : (head : ℤ) ∈ selectedCoordinates family j)
    (hC : ∀ u ∈ C, Q * (2 ^ width) ^ d ≤ u ∧ u < 2 * (Q * (2 ^ width) ^ d))
    (hcover : SumCover C K threshold) (hheavy : K ≤ (levelSlice earlier C B).card)
    (hthreshold : threshold ≤ (2 ^ width) ^ 2 * (Q * (2 ^ width) ^ d))
    (hB : RepeatedSumFree ((2 ^ width) ^ 6) B) :
    ¬DyadicMean (selectedCoordinates family) ((a : ℤ) + 2 ^ (d + H.val)) j head := by
  have hheadMem := selectedCoordinateWord_mem family hhead
  apply selected_head_not_dyadic_mean amplification H (selectedCoordinates family)
    (selectedCoordinateWord family) C B hwidth hQ hbase hamp hj hdelay hD halign
    hindexLower hindexUpper
  · intro k t ht
    exact hframe k t _ (selectedCoordinateWord_mem family ht)
  · intro k t ht h hh
    exact (hfixed k t _ (selectedCoordinateWord_mem family ht) h hh).trans
      (hfixed j head _ hheadMem h hh).symm
  · intro k t ht
    exact hselected k t _ (selectedCoordinateWord_mem family ht)
  · exact hhead
  · exact hC
  · exact hcover
  · exact hheavy
  · exact hthreshold
  · exact hB

end Erdos790.Upper
