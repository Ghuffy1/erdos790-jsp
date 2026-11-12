import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic

/-!
# Coordinates and word choices in a selected subfamily
-/

namespace Erdos790.Upper

def selectedCoordinates {d : ℕ} (family : ℕ → Finset (ℤ × (Fin d → Fin 2)))
    (j : ℕ) : Finset ℤ := (family j).image Prod.fst

noncomputable def selectedCoordinateWord {d : ℕ}
    (family : ℕ → Finset (ℤ × (Fin d → Fin 2))) (j : ℕ) (t : ℤ) : Fin d → Fin 2 :=
  if h : ∃ word, (t, word) ∈ family j then Classical.choose h else fun _ => 0

theorem selectedCoordinateWord_mem {d j : ℕ}
    (family : ℕ → Finset (ℤ × (Fin d → Fin 2))) {t : ℤ}
    (ht : t ∈ selectedCoordinates family j) : (t, selectedCoordinateWord family j t) ∈ family j := by
  classical
  have hexists : ∃ word, (t, word) ∈ family j := by
    obtain ⟨⟨u, word⟩, hword, hut⟩ := Finset.mem_image.mp ht
    change u = t at hut
    exact ⟨word, hut ▸ hword⟩
  simpa only [selectedCoordinateWord, dif_pos hexists] using Classical.choose_spec hexists

theorem selectedCoordinates_card {d j : ℕ}
    (family : ℕ → Finset (ℤ × (Fin d → Fin 2)))
    (hunique : ∀ t a b, (t, a) ∈ family j → (t, b) ∈ family j → a = b) :
    (selectedCoordinates family j).card = (family j).card := by
  classical
  apply Finset.card_image_of_injOn
  rintro ⟨t, a⟩ ha ⟨u, b⟩ hb htu
  change t = u at htu
  subst u
  exact Prod.ext rfl (hunique t a b ha hb)

end Erdos790.Upper
