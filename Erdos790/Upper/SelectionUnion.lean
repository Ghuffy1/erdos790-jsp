import Erdos790.Upper.SelectionMass
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Coordinate unions and their multiplicities over an interval of levels
-/

namespace Erdos790.Upper

def selectionIncidences (S : ℕ → Finset ℤ) (start stop : ℕ) : Finset (ℕ × ℤ) :=
  (Finset.range (stop - start)).biUnion fun i => (S (start + i)).image (fun x => (start + i, x))

theorem mem_selectionIncidences {S : ℕ → Finset ℤ} {start stop : ℕ} {p : ℕ × ℤ} :
    p ∈ selectionIncidences S start stop ↔ start ≤ p.1 ∧ p.1 < stop ∧ p.2 ∈ S p.1 := by
  constructor
  · intro hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    have := Finset.mem_range.mp hi
    exact ⟨by omega, by omega, hx⟩
  · rintro ⟨hstart, hstop, hp⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1 - start, Finset.mem_range.mpr (by omega), ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨p.2, by simpa only [Nat.add_sub_of_le hstart] using hp,
      by apply Prod.ext <;> simp only [Nat.add_sub_of_le hstart]⟩

theorem selectionIncidences_card (S : ℕ → Finset ℤ) (start stop : ℕ) :
    (selectionIncidences S start stop).card = selectionMass S start stop := by
  classical
  have hdisjoint : (Finset.range (stop - start) : Set ℕ).PairwiseDisjoint
      (fun i => (S (start + i)).image (fun x => (start + i, x))) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hpi
    obtain ⟨y, hy, hyp⟩ := Finset.mem_image.mp hpj
    have hlevels := congrArg (fun p : ℕ × ℤ => p.1) (hxp.trans hyp.symm)
    exact hij (by omega)
  have hcard (i : ℕ) : ((S (start + i)).image (fun x => (start + i, x))).card =
      (S (start + i)).card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    exact congrArg (fun p : ℕ × ℤ => p.2) hxy
  unfold selectionIncidences selectionMass
  rw [Finset.card_biUnion hdisjoint]
  simp only [hcard]

theorem selectionIncidences_mono {S : ℕ → Finset ℤ} {start a b : ℕ} (hab : a ≤ b) :
    selectionIncidences S start a ⊆ selectionIncidences S start b := by
  intro p hp
  obtain ⟨hstart, hstop, hmem⟩ := mem_selectionIncidences.mp hp
  exact mem_selectionIncidences.mpr ⟨hstart, hstop.trans_le hab, hmem⟩

def selectionCoordinateUnion (S : ℕ → Finset ℤ) (start stop : ℕ) : Finset ℤ :=
  (selectionIncidences S start stop).image Prod.snd

theorem mem_selectionCoordinateUnion {S : ℕ → Finset ℤ} {start stop : ℕ} {x : ℤ} :
    x ∈ selectionCoordinateUnion S start stop ↔ ∃ j, start ≤ j ∧ j < stop ∧ x ∈ S j := by
  constructor
  · intro hx
    obtain ⟨⟨j, y⟩, hmem, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨j, mem_selectionIncidences.mp hmem⟩
  · rintro ⟨j, hstart, hstop, hx⟩
    exact Finset.mem_image.mpr ⟨(j, x), mem_selectionIncidences.mpr ⟨hstart, hstop, hx⟩, rfl⟩

@[simp] theorem selectionCoordinateUnion_self (S : ℕ → Finset ℤ) (start : ℕ) :
    selectionCoordinateUnion S start start = ∅ := by
  simp [selectionCoordinateUnion, selectionIncidences]

theorem selectionMass_le_union {S : ℕ → Finset ℤ} {start finish stop multiplicity : ℕ}
    (hfinish : finish ≤ stop)
    (hcount : ∀ x, ((selectionIncidences S start stop).filter (fun p => p.2 = x)).card ≤ multiplicity) :
    selectionMass S start finish ≤ multiplicity * (selectionCoordinateUnion S start finish).card := by
  classical
  let E := selectionIncidences S start finish
  have hE : E ⊆ selectionIncidences S start stop := selectionIncidences_mono hfinish
  have hbound (x : ℤ) : (E.filter (fun p => p.2 = x)).card ≤ multiplicity := by
    calc
      _ ≤ ((selectionIncidences S start stop).filter (fun p => p.2 = x)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hE)
      _ ≤ multiplicity := hcount x
  rw [← selectionIncidences_card]
  change E.card ≤ multiplicity * (E.image Prod.snd).card
  calc
    E.card = ∑ x ∈ E.image Prod.snd, (E.filter (fun p => p.2 = x)).card :=
      Finset.card_eq_sum_card_image Prod.snd E
    _ ≤ ∑ _x ∈ E.image Prod.snd, multiplicity := Finset.sum_le_sum (fun x _ => hbound x)
    _ = _ := by simp [Nat.mul_comm]

end Erdos790.Upper
