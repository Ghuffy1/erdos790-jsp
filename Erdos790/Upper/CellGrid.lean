import Erdos790.Upper.CellPartitions

/-!
# The complete grid of equal-sized cells in a coordinate interval
-/

namespace Erdos790.Upper

def cellOccurrences {d : ℕ} (E : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (left : ℤ) (width index : ℕ) : Finset (ℕ × ℤ × (Fin d → Fin 2)) :=
  E.filter (fun p => (p.2.1 - left).toNat / width = index)

theorem cellOccurrences_subset {d : ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (left : ℤ) (width index : ℕ) :
    cellOccurrences E left width index ⊆ E := Finset.filter_subset _ _

theorem cell_index_bound {d width cells : ℕ} {left : ℤ}
    {p : ℕ × ℤ × (Fin d → Fin 2)} (hwidth : 0 < width)
    (hleft : left ≤ p.2.1) (hright : p.2.1 < left + (cells * width : ℕ)) :
    (p.2.1 - left).toNat / width < cells := by
  have hcast : ((p.2.1 - left).toNat : ℤ) = p.2.1 - left :=
    Int.toNat_of_nonneg (by omega)
  apply (Nat.div_lt_iff_lt_mul hwidth).mpr
  have hbound : ((p.2.1 - left).toNat : ℤ) < (cells * width : ℕ) := by omega
  exact_mod_cast hbound

theorem cellOccurrences_interval {d width index : ℕ} {left : ℤ}
    {E : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    (hwidth : 0 < width) (hleft : ∀ p ∈ E, left ≤ p.2.1) :
    ∀ p ∈ cellOccurrences E left width index,
      left + (index * width : ℕ) ≤ p.2.1 ∧
        p.2.1 < left + ((index + 1) * width : ℕ) := by
  intro p hp
  obtain ⟨hp, hindex⟩ := Finset.mem_filter.mp hp
  let n := (p.2.1 - left).toNat
  change n / width = index at hindex
  have hcast : (n : ℤ) = p.2.1 - left := Int.toNat_of_nonneg (by have := hleft p hp; omega)
  have hmod := Nat.mod_lt n hwidth
  have hidentity := Nat.mod_add_div n width
  rw [Nat.mul_comm width (n / width), hindex] at hidentity
  have hlo : index * width ≤ n := by omega
  have hhi : n < (index + 1) * width := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hloInt : ((index * width : ℕ) : ℤ) ≤ n := by exact_mod_cast hlo
  have hhiInt : (n : ℤ) < ((index + 1) * width : ℕ) := by exact_mod_cast hhi
  constructor <;> omega

theorem cellOccurrences_card_sum {d width cells : ℕ} {left : ℤ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (hwidth : 0 < width)
    (hframe : ∀ p ∈ E, left ≤ p.2.1 ∧ p.2.1 < left + (cells * width : ℕ)) :
    E.card = ∑ index ∈ Finset.range cells, (cellOccurrences E left width index).card := by
  classical
  apply Finset.card_eq_sum_card_fiberwise
    (f := fun p : ℕ × ℤ × (Fin d → Fin 2) => (p.2.1 - left).toNat / width)
  intro p hp
  exact Finset.mem_range.mpr (cell_index_bound hwidth (hframe p hp).1 (hframe p hp).2)

theorem dyadic_grid_dimensions {d h : ℕ} (hh : h < d) :
    2 ^ (d - h - 1) * (2 * 2 ^ (d + h)) = 2 ^ (2 * d) := by
  calc
    _ = 2 ^ (d - h - 1) * 2 ^ (d + h + 1) := by rw [pow_succ]; ac_rfl
    _ = 2 ^ ((d - h - 1) + (d + h + 1)) := (pow_add _ _ _).symm
    _ = _ := by congr 1; omega

end Erdos790.Upper
