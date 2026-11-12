import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

/-!
# Counting new integer midpoints inside one gap

Two adjacent boundary points provide the required parity. Every new midpoint
has at most two selected preimages, with one possible boundary exception.
-/

open Finset

namespace Erdos790.Upper

def midpointClosure (T S : Finset ℤ) : Finset ℤ :=
  T ∪ ((T ×ˢ S).filter fun xy => (xy.1 + xy.2) % 2 = 0).image
    (fun xy => (xy.1 + xy.2) / 2)

theorem half_image_card (S : Finset ℤ) (p : ℤ) :
    S.card ≤ 2 * (S.image fun x => (x + p) / 2).card := by
  apply Finset.card_le_mul_card_image S 2
  intro y _
  have hsubset : S.filter (fun x => (x + p) / 2 = y) ⊆
      {2 * y - p, 2 * y + 1 - p} := by
    intro x hx
    have heq := (Finset.mem_filter.mp hx).2
    have hcases : x = 2 * y - p ∨ x = 2 * y + 1 - p := by omega
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hcases
  exact (Finset.card_le_card hsubset).trans Finset.card_le_two

theorem boundary_half_mem_midpointClosure {T S : Finset ℤ} {p x : ℤ}
    (hp : p ∈ T) (hprev : p - 1 ∈ T) (hx : x ∈ S) :
    (x + p) / 2 ∈ midpointClosure T S := by
  let r := (x + p) % 2
  have hr : r = 0 ∨ r = 1 := by dsimp [r]; omega
  have hseed : p - r ∈ T := by
    rcases hr with hr | hr
    · simpa only [hr, sub_zero] using hp
    · simpa only [hr] using hprev
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨(p - r, x), ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hseed, hx⟩, ?_⟩
    dsimp [r]
    omega
  · dsimp [r]
    omega

theorem boundary_ceil_mem_midpointClosure {T S : Finset ℤ} {p x : ℤ}
    (hp : p ∈ T) (hnext : p + 1 ∈ T) (hx : x ∈ S) :
    (x + p + 1) / 2 ∈ midpointClosure T S := by
  let r := (x + p) % 2
  have hr : r = 0 ∨ r = 1 := by dsimp [r]; omega
  have hseed : p + r ∈ T := by
    rcases hr with hr | hr
    · simpa only [hr, add_zero] using hp
    · simpa only [hr] using hnext
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨(p + r, x), ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hseed, hx⟩, ?_⟩
    dsimp [r]
    omega
  · dsimp [r]
    omega

theorem erase_half_image_card (S : Finset ℤ) (p e : ℤ) :
    S.card ≤ 2 * ((S.erase e).image fun x => (x + p) / 2).card + 1 := by
  have hsize : S.card ≤ (S.erase e).card + 1 := by
    by_cases he : e ∈ S
    · exact (Finset.card_erase_add_one he).symm.le
    · rw [Finset.erase_eq_of_notMem he]
      omega
  have himage := half_image_card (S.erase e) p
  omega

theorem one_gap_midpoint_count {T S : Finset ℤ} {p q : ℤ}
    (hp : p ∈ T) (hprev : p - 1 ∈ T)
    (hS : ∀ x ∈ S, p < x ∧ x ≤ q)
    (hgap : ∀ x, p < x → x ≤ q → x ∉ T) :
    S.card ≤ 2 * (midpointClosure T S \ T).card + 1 := by
  let A := S.erase (p + 1)
  have hA : A ⊆ S := Finset.erase_subset _ _
  have hnew : A.image (fun x => (x + p) / 2) ⊆ midpointClosure T S \ T := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxS := hA hx
    have hxne := (Finset.mem_erase.mp hx).1
    obtain ⟨hpx, hxq⟩ := hS x hxS
    have hleft : p < (x + p) / 2 := by omega
    have hright : (x + p) / 2 ≤ q := by omega
    exact Finset.mem_sdiff.mpr
      ⟨boundary_half_mem_midpointClosure hp hprev hxS, hgap _ hleft hright⟩
  have hsize : S.card ≤ A.card + 1 := by
    by_cases hmem : p + 1 ∈ S
    · have hcard := Finset.card_erase_add_one hmem
      exact hcard.symm.le
    · have herase : A = S := Finset.erase_eq_of_notMem hmem
      rw [herase]
      omega
  have himage := half_image_card A p
  have himage_le := Finset.card_le_card hnew
  omega

end Erdos790.Upper
