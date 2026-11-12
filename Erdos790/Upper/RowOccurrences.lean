import Erdos790.Upper.SelectedPairs
import Erdos790.Upper.TentParameters
import Erdos790.Upper.MixedMeanResidual

/-!
# The actual selected coordinate occurrences in a translated row
-/

namespace Erdos790.Upper.AuxiliaryParameters

noncomputable def rowOccurrences (d : ℕ) (levels : Finset ℕ)
    (constant step : ℕ) (B : Finset ℕ) : Finset (ℕ × ℤ × (Fin d → Fin 2)) := by
  classical
  exact (levels.product ((Finset.Ico (0 : ℤ) (timeCount d)).product Finset.univ)).filter
    (fun p => 2 ^ p.1 * nativeTentValue (tentAmplification d) (2 ^ (6 * d)) constant
      (factorialModulus d) step p.2.1.toNat p.2.2 ∈ B)

theorem mem_rowOccurrences {d constant step j : ℕ} {levels : Finset ℕ} {B : Finset ℕ}
    {t : ℤ} {word : Fin d → Fin 2} :
    (j, t, word) ∈ rowOccurrences d levels constant step B ↔
      j ∈ levels ∧ 0 ≤ t ∧ t < timeCount d ∧
        2 ^ j * nativeTentValue (tentAmplification d) (2 ^ (6 * d)) constant
          (factorialModulus d) step t.toNat word ∈ B := by
  classical
  constructor
  · intro h
    obtain ⟨hproduct, hselected⟩ := Finset.mem_filter.mp h
    obtain ⟨hj, hcoordinates⟩ := Finset.mem_product.mp hproduct
    obtain ⟨ht, hword⟩ := Finset.mem_product.mp hcoordinates
    exact ⟨hj, (Finset.mem_Ico.mp ht).1, (Finset.mem_Ico.mp ht).2, hselected⟩
  · rintro ⟨hj, hlo, hhi, hselected⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hj, Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hlo, hhi⟩, Finset.mem_univ _⟩⟩,
      hselected⟩

theorem nativeTentValue_row (d constant : ℕ) (t : Fin (timeCount d)) (word : Fin d → Fin 2) :
    nativeTentValue (tentAmplification d) (2 ^ (6 * d)) constant (factorialModulus d)
      (rowStep d) t.val word =
      constant + rowOffset (factorialModulus d) (rowStep d) (radixBase d)
        (tentRow d (tentAmplification d)) (t, word) := rfl

theorem translated_rows_cover_selected {d J : ℕ} (offset : Fin J → ℕ)
    (levels : Finset ℕ) (B : Finset ℕ) :
    ∀ j ∈ levels, ∀ u ∈ levelSlice j
      (translatedHost (baseRange d) offset (tentTranslations d (tentAmplification d))) B,
      ∃ i t word,
        (j, t, word) ∈ rowOccurrences d levels (baseRange d + offset i) (rowStep d) B ∧
        nativeTentValue (tentAmplification d) (2 ^ (6 * d)) (baseRange d + offset i)
          (factorialModulus d) (rowStep d) t.toNat word = u := by
  classical
  intro j hj u hu
  obtain ⟨hu, hB⟩ := Finset.mem_filter.mp hu
  obtain ⟨⟨i, z⟩, hi, rfl⟩ := Finset.mem_image.mp hu
  have hz := z.property
  obtain ⟨⟨t, word⟩, ht, hvalue⟩ := Finset.mem_image.mp hz
  have heq : nativeTentValue (tentAmplification d) (2 ^ (6 * d)) (baseRange d + offset i)
      (factorialModulus d) (rowStep d) t.val word = baseRange d + offset i + z.val := by
    rw [nativeTentValue_row, hvalue]
  refine ⟨i, (t.val : ℤ), word, ?_, ?_⟩
  · apply mem_rowOccurrences.mpr
    exact ⟨hj, by positivity, by exact_mod_cast t.isLt, by simpa only [Int.toNat_natCast, heq] using hB⟩
  · simpa only [Int.toNat_natCast] using heq

end Erdos790.Upper.AuxiliaryParameters
