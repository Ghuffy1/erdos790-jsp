import Erdos790.Upper.ProgressionCounts
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting progressions in integer affine images

The finite extremal hypothesis in this file is supplied by the quantitative
three-term progression theorem. All counting and the transfer to many
centered pairs are elementary.
-/

open Finset

namespace Erdos790.Upper

def natProgressionPairs (T : Finset ℕ) : Finset (ℕ × ℕ) :=
  (T ×ˢ T).filter fun p => p.1 < p.2 ∧ ∃ y ∈ T, p.1 + y = 2 * p.2

def ThreeTermExtremalBound (M k : ℕ) : Prop :=
  ∀ T ⊆ Finset.Icc 1 M, natProgressionPairs T = ∅ → T.card ≤ k

theorem cardinal_le_extremal_add_pairs {M k : ℕ}
    (hbound : ThreeTermExtremalBound M k) {T : Finset ℕ}
    (hT : T ⊆ Finset.Icc 1 M) : T.card ≤ k + (natProgressionPairs T).card := by
  classical
  let centers := (natProgressionPairs T).image Prod.snd
  have hcenters : centers ⊆ T := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  have hfree : natProgressionPairs (T \ centers) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpair, hlt, y, hy, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hz⟩ := Finset.mem_product.mp hpair
    have hpT : p ∈ natProgressionPairs T := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hz).1⟩,
        hlt, y, (Finset.mem_sdiff.mp hy).1, heq⟩
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_image.mpr ⟨p, hpT, rfl⟩)
  have hsmall := hbound (T \ centers) (Finset.sdiff_subset.trans hT) hfree
  have hpartition := Finset.card_sdiff_add_card_eq_card hcenters
  have hcard : centers.card ≤ (natProgressionPairs T).card := Finset.card_image_le
  omega

def affineIndexSet (S : Finset ℤ) (M : ℕ) (a : ℤ) (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter fun i => a + (i : ℤ) * q ∈ S

def affineParameters (N D : ℕ) : Finset (ℤ × ℕ) :=
  Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc 1 D

def affineIncidences (S : Finset ℤ) (N M D : ℕ) : Finset ((ℤ × ℕ) × ℕ) :=
  (affineParameters N D ×ˢ Finset.Icc 1 M).filter
    fun p => p.1.1 + (p.2 : ℤ) * p.1.2 ∈ S

theorem affineIncidences_card_sum (S : Finset ℤ) (N M D : ℕ) :
    (affineIncidences S N M D).card =
      ∑ p ∈ affineParameters N D, (affineIndexSet S M p.1 p.2).card := by
  classical
  simp only [affineIncidences, affineIndexSet, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

theorem affineIncidences_card {S : Finset ℤ} {N M D : ℕ}
    (hS : S ⊆ Finset.Icc 1 (N : ℤ)) (hMD : M * D ≤ N) :
    (affineIncidences S N M D).card = S.card * M * D := by
  classical
  have hbij : (affineIncidences S N M D).card =
      (S ×ˢ (Finset.Icc 1 M ×ˢ Finset.Icc 1 D)).card := by
    apply Finset.card_bij
      (fun p _ => (p.1.1 + (p.2 : ℤ) * p.1.2, (p.2, p.1.2)))
    · intro p hp
      obtain ⟨hpbase, hpS⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpParam, hi⟩ := Finset.mem_product.mp hpbase
      have hq := (Finset.mem_product.mp hpParam).2
      exact Finset.mem_product.mpr ⟨hpS, Finset.mem_product.mpr ⟨hi, hq⟩⟩
    · intro p hp r hr heq
      have hvalue := congrArg Prod.fst heq
      have hindex := congrArg (fun x : ℤ × (ℕ × ℕ) => x.2.1) heq
      have hstep := congrArg (fun x : ℤ × (ℕ × ℕ) => x.2.2) heq
      apply Prod.ext
      · apply Prod.ext
        · dsimp at hvalue hindex hstep
          rw [hindex, hstep] at hvalue
          omega
        · exact hstep
      · exact hindex
    · intro p hp
      obtain ⟨hx, hiq⟩ := Finset.mem_product.mp hp
      obtain ⟨hi, hq⟩ := Finset.mem_product.mp hiq
      obtain ⟨hi1, hiM⟩ := Finset.mem_Icc.mp hi
      obtain ⟨hq1, hqD⟩ := Finset.mem_Icc.mp hq
      obtain ⟨hx1, hxN⟩ := Finset.mem_Icc.mp (hS hx)
      have hprodNat : p.2.1 * p.2.2 ≤ N :=
        (Nat.mul_le_mul hiM hqD).trans hMD
      have hprod : (p.2.1 : ℤ) * p.2.2 ≤ N := by exact_mod_cast hprodNat
      have hprod0 : (0 : ℤ) ≤ (p.2.1 : ℤ) * p.2.2 := by positivity
      refine ⟨((p.1 - (p.2.1 : ℤ) * p.2.2, p.2.2), p.2.1), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, hi⟩, ?_⟩
        · apply Finset.mem_product.mpr
          exact ⟨Finset.mem_Icc.mpr ⟨by dsimp; omega, by dsimp; omega⟩, hq⟩
        · simpa only [sub_add_cancel] using hx
      · simp
  simpa only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel,
    Nat.mul_assoc] using hbij

def affineProgressions (S : Finset ℤ) (N M D : ℕ) :
    Finset ((ℤ × ℕ) × (ℕ × ℕ)) :=
  (affineParameters N D ×ˢ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M)).filter
    fun p => p.2 ∈ natProgressionPairs (affineIndexSet S M p.1.1 p.1.2)

theorem affineProgressions_card_sum (S : Finset ℤ) (N M D : ℕ) :
    (affineProgressions S N M D).card =
      ∑ p ∈ affineParameters N D,
        (natProgressionPairs (affineIndexSet S M p.1 p.2)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := affineProgressions S N M D) (t := affineParameters N D) (f := Prod.fst)
    (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.card_bij (fun q _ => q.2)
  · intro q hq
    obtain ⟨hqglobal, hqp⟩ := Finset.mem_filter.mp hq
    have hqAP := (Finset.mem_filter.mp hqglobal).2
    change q.1 = p at hqp
    simpa only [hqp] using hqAP
  · intro q hq r hr heq
    have hqp := (Finset.mem_filter.mp hq).2
    have hrp := (Finset.mem_filter.mp hr).2
    exact Prod.ext (hqp.trans hrp.symm) heq
  · intro q hq
    have hqindices := (Finset.mem_filter.mp hq).1
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hqindices
    have hbase : (p, q) ∈ affineParameters N D ×ˢ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M) :=
      Finset.mem_product.mpr ⟨hp, Finset.mem_product.mpr
        ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hj).1⟩⟩
    refine ⟨(p, q), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
    exact Finset.mem_filter.mpr ⟨hbase, hq⟩

end Erdos790.Upper
