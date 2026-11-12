import Erdos790.Upper.OccurrenceFamilies
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Partitioning a selected family by the bits outside its free positions
-/

namespace Erdos790.Upper

def exteriorProfile {d : ℕ} (free : Finset (Fin d)) (word : Fin d → Fin 2) :
    (↥(freeᶜ : Finset (Fin d))) → Fin 2 := fun h => word h.val

def fillExterior {d : ℕ} (free : Finset (Fin d))
    (profile : (↥(freeᶜ : Finset (Fin d))) → Fin 2) (h : Fin d) : Fin 2 :=
  if hh : h ∈ (freeᶜ : Finset (Fin d)) then profile ⟨h, hh⟩ else 0

noncomputable def profileOccurrences {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (free : Finset (Fin d))
    (profile : (↥(freeᶜ : Finset (Fin d))) → Fin 2) :
    Finset (ℕ × ℤ × (Fin d → Fin 2)) := by
  classical
  exact E.filter (fun p => exteriorProfile free p.2.2 = profile)

theorem profileOccurrences_subset {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (free : Finset (Fin d))
    (profile : (↥(freeᶜ : Finset (Fin d))) → Fin 2) :
    profileOccurrences E free profile ⊆ E := Finset.filter_subset _ _

theorem profileOccurrences_fixed {d : ℕ}
    {E : Finset (ℕ × ℤ × (Fin d → Fin 2))} (free : Finset (Fin d))
    (profile : (↥(freeᶜ : Finset (Fin d))) → Fin 2) :
    ∀ p ∈ profileOccurrences E free profile, ∀ h, h ∉ free →
      p.2.2 h = fillExterior free profile h := by
  intro p hp h hh
  have hprofile := (Finset.mem_filter.mp hp).2
  have hcompl : h ∈ (freeᶜ : Finset (Fin d)) := Finset.mem_compl.mpr hh
  have heq := congrFun hprofile ⟨h, hcompl⟩
  simpa only [exteriorProfile, fillExterior, dif_pos hcompl] using heq

theorem exteriorProfiles_card {d : ℕ} (free : Finset (Fin d)) :
    Fintype.card ((↥(freeᶜ : Finset (Fin d))) → Fin 2) = 2 ^ (d - free.card) := by
  simp

theorem profileOccurrences_card_sum {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (free : Finset (Fin d)) :
    E.card = ∑ profile : (↥(freeᶜ : Finset (Fin d))) → Fin 2,
      (profileOccurrences E free profile).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise
    (s := E) (t := (Finset.univ : Finset ((↥(freeᶜ : Finset (Fin d))) → Fin 2)))
    (f := fun p : ℕ × ℤ × (Fin d → Fin 2) => exteriorProfile free p.2.2)
    (fun p hp => Finset.mem_univ _)

theorem profileOccurrences_card_bound {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (free : Finset (Fin d)) (bound : ℝ)
    (hbound : ∀ profile : (↥(freeᶜ : Finset (Fin d))) → Fin 2,
      ((profileOccurrences E free profile).card : ℝ) ≤ bound) :
    (E.card : ℝ) ≤ (2 : ℝ) ^ (d - free.card) * bound := by
  classical
  have hsum : (E.card : ℝ) = ∑ profile : (↥(freeᶜ : Finset (Fin d))) → Fin 2,
      ((profileOccurrences E free profile).card : ℝ) := by
    exact_mod_cast profileOccurrences_card_sum E free
  rw [hsum]
  calc
    _ ≤ ∑ _profile : (↥(freeᶜ : Finset (Fin d))) → Fin 2, bound :=
      Finset.sum_le_sum (fun profile _ => hbound profile)
    _ = (Fintype.card ((↥(freeᶜ : Finset (Fin d))) → Fin 2) : ℝ) * bound := by simp
    _ = _ := by rw [exteriorProfiles_card]; norm_cast

end Erdos790.Upper
