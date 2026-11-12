import Erdos790.Upper.CellGrid
import Mathlib.Algebra.Order.Group.Abs

/-!
# Choosing the earlier and later halves of a cell
-/

namespace Erdos790.Upper

def halfOccurrences {d : ℕ} (E : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (cut : ℤ) (right : Bool) : Finset (ℕ × ℤ × (Fin d → Fin 2)) :=
  E.filter (fun p => if right then cut ≤ p.2.1 else p.2.1 < cut)

def halfStart (left : ℤ) (size : ℕ) (right : Bool) : ℤ :=
  if right then left + size else left

theorem halfOccurrences_subset {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (cut : ℤ) (right : Bool) :
    halfOccurrences E cut right ⊆ E := Finset.filter_subset _ _

theorem halfOccurrences_card_split {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (cut : ℤ) (right : Bool) :
    E.card = (halfOccurrences E cut right).card + (halfOccurrences E cut (!right)).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := E) (fun p => p.2.1 < cut)
  cases right <;> simp only [halfOccurrences, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, not_lt] at * <;> omega

theorem halfOccurrences_interval {d size : ℕ} {left : ℤ}
    {E : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    (hframe : ∀ p ∈ E, left ≤ p.2.1 ∧ p.2.1 < left + 2 * (size : ℤ)) (right : Bool) :
    ∀ p ∈ halfOccurrences E (left + size) right,
      halfStart left size right ≤ p.2.1 ∧ p.2.1 < halfStart left size right + size := by
  intro p hp
  obtain ⟨hp, hside⟩ := Finset.mem_filter.mp hp
  have hbounds := hframe p hp
  cases right <;> simp only [halfStart, Bool.false_eq_true,
    ite_false, ite_true] at * <;> omega

theorem anchor_mem_half {d : ℕ} {E : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    {anchor : ℕ × ℤ × (Fin d → Fin 2)} (hanchor : anchor ∈ E) (cut : ℤ) :
    anchor ∈ halfOccurrences E cut (decide (cut ≤ anchor.2.1)) := by
  classical
  by_cases hcut : cut ≤ anchor.2.1
  · simp [halfOccurrences, hcut, hanchor]
  · have hlt : anchor.2.1 < cut := lt_of_not_ge hcut
    simp [halfOccurrences, hcut, hlt, hanchor]

theorem opposite_half_relation {d : ℕ} {E : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    {anchor p : ℕ × ℤ × (Fin d → Fin 2)} {cut : ℤ} {right : Bool}
    (hanchor : anchor ∈ halfOccurrences E cut right)
    (hp : p ∈ halfOccurrences E cut (!right)) :
    (anchor.2.1 < cut ∧ cut ≤ p.2.1) ∨ (cut ≤ anchor.2.1 ∧ p.2.1 < cut) := by
  have ha := (Finset.mem_filter.mp hanchor).2
  have hb := (Finset.mem_filter.mp hp).2
  cases right <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ite_false, ite_true] at *
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩

theorem halfStart_dvd {left : ℤ} {size : ℕ} (h : (size : ℤ) ∣ left) (right : Bool) :
    (size : ℤ) ∣ halfStart left size right := by
  cases right
  · exact h
  · exact dvd_add h (dvd_refl _)

theorem cell_coordinate_distance {d size : ℕ} {left : ℤ}
    {E : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    (hframe : ∀ p ∈ E, left ≤ p.2.1 ∧ p.2.1 < left + 2 * (size : ℤ))
    {a b : ℕ × ℤ × (Fin d → Fin 2)} (ha : a ∈ E) (hb : b ∈ E) :
    |a.2.1 - b.2.1| ≤ 2 * (size : ℤ) := by
  have hleft := hframe a ha
  have hright := hframe b hb
  rw [abs_le]
  constructor <;> omega

theorem dyadic_grid_size {small big : ℕ} (h : small ≤ big) :
    (2 : ℕ) ^ (big - small) * 2 ^ small = 2 ^ big := by
  rw [← pow_add, Nat.sub_add_cancel h]

theorem integer_power_dvd {small big : ℕ} (h : small ≤ big) :
    (2 : ℤ) ^ small ∣ (2 : ℤ) ^ big := by
  refine ⟨(2 : ℤ) ^ (big - small), ?_⟩
  rw [← pow_add]
  congr 1
  omega

end Erdos790.Upper
