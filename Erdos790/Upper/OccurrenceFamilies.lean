import Erdos790.Upper.CoordinateFamilies
import Erdos790.Upper.SelectionUnion

/-!
# Finite occurrence sets and their level-by-level coordinate families
-/

namespace Erdos790.Upper

def occurrenceFamily {d : ℕ} (E : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (j : ℕ) : Finset (ℤ × (Fin d → Fin 2)) :=
  (E.filter (fun p => p.1 = j)).image Prod.snd

theorem mem_occurrenceFamily {d j : ℕ} {E : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    {p : ℤ × (Fin d → Fin 2)} : p ∈ occurrenceFamily E j ↔ (j, p) ∈ E := by
  classical
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
    obtain ⟨hq, hqj⟩ := Finset.mem_filter.mp hq
    have heq : q = (j, p) := Prod.ext hqj hqp
    simpa only [heq] using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨(j, p), Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩

theorem mem_occurrenceCoordinates {d j : ℕ} {E : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    {t : ℤ} : t ∈ selectedCoordinates (occurrenceFamily E) j ↔
      ∃ word, (j, t, word) ∈ E := by
  classical
  constructor
  · intro ht
    obtain ⟨⟨u, word⟩, hword, hut⟩ := Finset.mem_image.mp ht
    change u = t at hut
    subst u
    exact ⟨word, mem_occurrenceFamily.mp hword⟩
  · rintro ⟨word, hword⟩
    exact Finset.mem_image.mpr ⟨(t, word), mem_occurrenceFamily.mpr hword, rfl⟩

theorem occurrenceFamily_mono {d : ℕ} {E F : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    (hEF : E ⊆ F) (j : ℕ) : occurrenceFamily E j ⊆ occurrenceFamily F j := by
  intro p hp
  exact mem_occurrenceFamily.mpr (hEF (mem_occurrenceFamily.mp hp))

theorem occurrence_incidences {d start stop : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (hlevels : ∀ p ∈ E, start ≤ p.1 ∧ p.1 < stop) :
    selectionIncidences (selectedCoordinates (occurrenceFamily E)) start stop =
      E.image (fun p => (p.1, p.2.1)) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hstart, hstop, hmem⟩ := mem_selectionIncidences.mp hp
    obtain ⟨word, hword⟩ := mem_occurrenceCoordinates.mp hmem
    exact Finset.mem_image.mpr ⟨(p.1, p.2, word), hword, Prod.eta p⟩
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hstart, hstop⟩ := hlevels q hq
    exact mem_selectionIncidences.mpr ⟨hstart, hstop,
      mem_occurrenceCoordinates.mpr ⟨q.2.2, hq⟩⟩

theorem occurrence_mass_eq {d start stop : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (hlevels : ∀ p ∈ E, start ≤ p.1 ∧ p.1 < stop)
    (hunique : ∀ j t a b, (j, t, a) ∈ E → (j, t, b) ∈ E → a = b) :
    E.card = selectionMass (selectedCoordinates (occurrenceFamily E)) start stop := by
  classical
  rw [← selectionIncidences_card, occurrence_incidences E hlevels]
  symm
  apply Finset.card_image_of_injOn
  rintro ⟨ja, ta, wa⟩ ha ⟨jb, tb, wb⟩ hb hab
  have hlevel : ja = jb := congrArg (fun p : ℕ × ℤ => p.1) hab
  have hcoordinate : ta = tb := congrArg (fun p : ℕ × ℤ => p.2) hab
  subst jb
  subst tb
  exact Prod.ext rfl (Prod.ext rfl (hunique ja ta wa wb ha hb))

end Erdos790.Upper
