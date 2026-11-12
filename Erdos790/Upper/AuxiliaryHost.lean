import Erdos790.Upper.AuxiliaryOffsets
import Erdos790.Upper.DenseTranslatedCover

/-!
# The uniform sum property for a prescribed deterministic translation set
-/

namespace Erdos790.Upper.AuxiliaryParameters

def coefficientRange (d : ℕ) : ℕ := 100 * roughScale d ^ 2
noncomputable def sumThreshold (d : ℕ) : ℕ :=
  2 * sampleSize d * coefficientRange d * baseRange d

theorem auxiliary_host_exists {d : ℕ} (hd : 0 < d) (translations : Finset ℕ)
    (hne : translations.Nonempty) (hcard : translations.card ≤ 2 ^ (3 * d))
    (hdiv : ∀ z ∈ translations, factorialModulus d ∣ z)
    (hbound : ∀ z ∈ translations, z < blockCount d * factorialModulus d) :
    ∃ offset : Fin (sampleSize d) → ℕ,
      (∀ i, offset i < blockCount d * factorialModulus d ∧
        Nat.Coprime (offset i) (factorialModulus d)) ∧
      Function.Injective (fun i => offset i % factorialModulus d) ∧
      (translatedHost (baseRange d) offset translations).card =
        sampleSize d * translations.card ∧
      (∀ x ∈ translatedHost (baseRange d) offset translations,
        baseRange d ≤ x ∧ x < 2 * baseRange d ∧ Nat.Coprime x (factorialModulus d)) ∧
      SumCover (translatedHost (baseRange d) offset translations)
        (2 * sampleExponent d * translations.card) (sumThreshold d) := by
  obtain ⟨offset, hoffset, hinjective, hphase⟩ := auxiliary_offsets_exist hd translations hcard
  have hXdiv : factorialModulus d ∣ baseRange d :=
    ⟨2 ^ (6 * d ^ 2), rfl⟩
  have hX := baseRange_eq_four_blocks hd
  have hXpos := baseRange_pos d
  have htestLower : 2 * baseRange d ≤ testCount d := by
    have hfirst : 2 * baseRange d ≤ 4 * baseRange d ^ 2 := by nlinarith
    exact hfirst.trans (Nat.le_mul_of_pos_right _ (by positivity : 0 < 2 ^ (3 * d)))
  have htail : ((2 * baseRange d : ℕ) : ℝ) * (1 / 200 : ℝ) ^ sampleExponent d < 1 :=
    geometric_tail_of_sample_budget (Nat.cast_nonneg _) (by exact_mod_cast htestLower)
      (test_budget d)
  have hv : 0 < roughScale d := by have h := roughScale_large d; omega
  have hp : (0 : ℝ) < (roughScale d ^ 2 : ℕ) := by
    exact_mod_cast Nat.pow_pos hv
  have hB : 100 * ((roughScale d ^ 2 : ℕ) : ℝ) ≤ coefficientRange d := by
    simp only [coefficientRange, Nat.cast_mul, Nat.cast_ofNat]
    exact le_rfl
  refine ⟨offset, hoffset, hinjective,
    translatedHost_card offset translations hXdiv hdiv hinjective, ?_, ?_⟩
  · intro x hx
    obtain ⟨hlow, hhigh⟩ := translatedHost_bounds offset translations hX
      (fun i => (hoffset i).1) hbound hx
    exact ⟨hlow, hhigh, translatedHost_coprime offset translations hXdiv hdiv
      (fun i => (hoffset i).2) hx⟩
  · exact translatedHost_sumCover offset translations hne hXpos hX hXdiv hdiv
      hoffset hbound hinjective (sampleExponent_pos d) hp hB htail hphase

end Erdos790.Upper.AuxiliaryParameters
