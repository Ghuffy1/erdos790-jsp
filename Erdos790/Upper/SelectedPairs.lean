import Erdos790.Upper.Layers
import Erdos790.Upper.OccurrenceFamilies

/-!
# Covering selected level-value pairs by the coordinate rows
-/

namespace Erdos790.Upper

def selectedPairs (levels : Finset ℕ) (C B : Finset ℕ) : Finset (ℕ × ℕ) :=
  levels.biUnion (fun j => (levelSlice j C B).image (fun u => (j, u)))

theorem selectedPairs_card (levels : Finset ℕ) (C B : Finset ℕ) :
    (selectedPairs levels C B).card = ∑ j ∈ levels, (levelSlice j C B).card := by
  classical
  have hdisjoint : (levels : Set ℕ).PairwiseDisjoint
      (fun j => (levelSlice j C B).image (fun u => (j, u))) := by
    intro j hj k hk hne
    apply Finset.disjoint_left.mpr
    intro p hpj hpk
    obtain ⟨u, hu, hup⟩ := Finset.mem_image.mp hpj
    obtain ⟨v, hv, hvp⟩ := Finset.mem_image.mp hpk
    exact hne (congrArg Prod.fst (hup.trans hvp.symm))
  unfold selectedPairs
  rw [Finset.card_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.card_image_of_injective
  intro u v huv
  exact congrArg Prod.snd huv

theorem selected_mass_le_row_occurrences {d J : ℕ} (levels : Finset ℕ) (C B : Finset ℕ)
    (rows : Fin J → Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (value : Fin J → ℤ → (Fin d → Fin 2) → ℕ)
    (hcover : ∀ j ∈ levels, ∀ u ∈ levelSlice j C B,
      ∃ i t word, (j, t, word) ∈ rows i ∧ value i t word = u) :
    (∑ j ∈ levels, (levelSlice j C B).card) ≤ ∑ i : Fin J, (rows i).card := by
  classical
  let images := fun i => (rows i).image (fun p => (p.1, value i p.2.1 p.2.2))
  have hsubset : selectedPairs levels C B ⊆ Finset.univ.biUnion images := by
    intro p hp
    obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i, t, word, hmem, hvalue⟩ := hcover j hj u hu
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨(j, t, word), hmem, by simp only [hvalue]⟩⟩
  rw [← selectedPairs_card]
  calc
    _ ≤ (Finset.univ.biUnion images).card := Finset.card_le_card hsubset
    _ ≤ ∑ i : Fin J, (images i).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin J, (rows i).card := Finset.sum_le_sum (fun i hi => Finset.card_image_le)

end Erdos790.Upper
