import Erdos790.Upper.CellSides

/-!
# Natural endpoints and alignment of recursive dyadic cells
-/

namespace Erdos790.Upper

def halfCellStart (left size : ℕ) (right : Bool) : ℕ :=
  if right then left + size else left

theorem halfCellStart_cast (left size : ℕ) (right : Bool) :
    (halfCellStart left size right : ℤ) = halfStart (left : ℤ) size right := by
  cases right <;> simp [halfCellStart, halfStart]

theorem halfCellStart_dvd {left size : ℕ} (h : size ∣ left) (right : Bool) :
    size ∣ halfCellStart left size right := by
  cases right
  · exact h
  · exact dvd_add h (dvd_refl _)

theorem natural_power_dvd {small big : ℕ} (h : small ≤ big) :
    (2 : ℕ) ^ small ∣ (2 : ℕ) ^ big := by
  refine ⟨2 ^ (big - small), ?_⟩
  rw [← pow_add]
  congr 1
  omega

theorem grid_start_dvd {small big left index : ℕ}
    (h : small ≤ big) (hleft : 2 ^ big ∣ left) :
    2 ^ small ∣ left + index * 2 ^ small := by
  apply dvd_add ((natural_power_dvd h).trans hleft)
  exact ⟨index, by ring⟩

theorem cellOccurrences_nat_interval {d width index left : ℕ}
    {E : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    (hwidth : 0 < width) (hleft : ∀ p ∈ E, (left : ℤ) ≤ p.2.1) :
    ∀ p ∈ cellOccurrences E (left : ℤ) width index,
      ((left + index * width : ℕ) : ℤ) ≤ p.2.1 ∧
        p.2.1 < ((left + index * width + width : ℕ) : ℤ) := by
  intro p hp
  have h := cellOccurrences_interval hwidth hleft p hp
  simpa only [Nat.add_mul, Nat.one_mul, Nat.cast_add, add_assoc] using h

end Erdos790.Upper
