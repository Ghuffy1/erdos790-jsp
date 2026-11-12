import Erdos790.Upper.OccurrenceFamilies

/-!
# Exact half-cell and binary-profile partitions of selected occurrences
-/

namespace Erdos790.Upper

def intervalOccurrences {d : ℕ} (E : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (left right : ℤ) : Finset (ℕ × ℤ × (Fin d → Fin 2)) :=
  E.filter (fun p => left ≤ p.2.1 ∧ p.2.1 < right)

theorem intervalOccurrences_subset {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (left right : ℤ) :
    intervalOccurrences E left right ⊆ E := Finset.filter_subset _ _

theorem intervalOccurrences_card_split {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) {left cut right : ℤ}
    (hleft : left ≤ cut) (hright : cut ≤ right) :
    (intervalOccurrences E left right).card =
      (intervalOccurrences E left cut).card + (intervalOccurrences E cut right).card := by
  classical
  let A := intervalOccurrences E left right
  have hfirst : A.filter (fun p => p.2.1 < cut) = intervalOccurrences E left cut := by
    ext p
    simp only [A, intervalOccurrences, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, hlo, _⟩, hcut⟩
      exact ⟨hp, hlo, hcut⟩
    · rintro ⟨hp, hlo, hcut⟩
      exact ⟨⟨hp, hlo, hcut.trans_le hright⟩, hcut⟩
  have hsecond : A.filter (fun p => ¬p.2.1 < cut) = intervalOccurrences E cut right := by
    ext p
    simp only [A, intervalOccurrences, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, _, hhi⟩, hcut⟩
      exact ⟨hp, le_of_not_gt hcut, hhi⟩
    · rintro ⟨hp, hcut, hhi⟩
      exact ⟨⟨hp, hleft.trans hcut, hhi⟩, not_lt.mpr hcut⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun p => p.2.1 < cut)
  rw [hfirst, hsecond] at hsplit
  exact hsplit.symm

def bitOccurrences {d : ℕ} (E : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (H : Fin d) (bit : Fin 2) : Finset (ℕ × ℤ × (Fin d → Fin 2)) :=
  E.filter (fun p => p.2.2 H = bit)

theorem bitOccurrences_subset {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (H : Fin d) (bit : Fin 2) :
    bitOccurrences E H bit ⊆ E := Finset.filter_subset _ _

theorem bitOccurrences_card_split {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (H : Fin d) :
    E.card = (bitOccurrences E H 0).card + (bitOccurrences E H 1).card := by
  classical
  have hnot (p : ℕ × ℤ × (Fin d → Fin 2)) : p.2.2 H ≠ 0 ↔ p.2.2 H = 1 := by
    constructor
    · intro hz
      have hval : (p.2.2 H).val ≠ 0 := by
        intro heq
        exact hz (Fin.ext heq)
      have hlt := (p.2.2 H).isLt
      apply Fin.ext
      change (p.2.2 H).val = 1
      omega
    · intro heq
      rw [heq]
      decide
  have hsecond : E.filter (fun p => ¬p.2.2 H = 0) = bitOccurrences E H 1 := by
    ext p
    simp only [bitOccurrences, Finset.mem_filter, hnot]
  have hsplit := Finset.card_filter_add_card_filter_not (s := E) (fun p => p.2.2 H = 0)
  rw [hsecond] at hsplit
  exact hsplit.symm

theorem bitOccurrences_fixed {d : ℕ}
    {E : Finset (ℕ × ℤ × (Fin d → Fin 2))} {free : Finset (Fin d)}
    {fixed : Fin d → Fin 2} (H : Fin d) (bit : Fin 2)
    (hfixed : ∀ p ∈ E, ∀ h, h ∉ free → p.2.2 h = fixed h) :
    ∀ p ∈ bitOccurrences E H bit, ∀ h, h ∉ free.erase H →
      p.2.2 h = Function.update fixed H bit h := by
  intro p hp h hh
  obtain ⟨hp, hbit⟩ := Finset.mem_filter.mp hp
  by_cases hH : h = H
  · subst h
    simpa only [Function.update_self] using hbit
  · have hnot : h ∉ free := by
      intro hmem
      exact hh (Finset.mem_erase.mpr ⟨hH, hmem⟩)
    simpa only [Function.update_of_ne hH] using hfixed p hp h hnot

end Erdos790.Upper
