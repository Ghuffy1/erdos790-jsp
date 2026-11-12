import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
# Dyadic layers of the coarse host

The base interval `[X, 2*X)` separates distinct dyadic layers. Selection in
the layered host therefore has an exact decomposition into base-set slices.
-/

open Finset

namespace Erdos790.Upper

def dyadicDilate (j : ℕ) (C : Finset ℕ) : Finset ℕ :=
  C.image fun u => 2 ^ j * u

def layeredHost (L : ℕ) (C : Finset ℕ) : Finset ℕ :=
  (Finset.range L).biUnion fun j => dyadicDilate j C

def levelSlice (j : ℕ) (C B : Finset ℕ) : Finset ℕ :=
  C.filter fun u => 2 ^ j * u ∈ B

theorem dyadic_scaled_lt {X u v j k : ℕ} (hu : u < 2 * X) (hv : X ≤ v)
    (hjk : j < k) : 2 ^ j * u < 2 ^ k * v := by
  calc
    2 ^ j * u < 2 ^ j * (2 * X) :=
      Nat.mul_lt_mul_of_pos_left hu (Nat.two_pow_pos j)
    _ = 2 ^ (j + 1) * X := by rw [pow_succ]; ac_rfl
    _ ≤ 2 ^ k * X := Nat.mul_le_mul_right X
      (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
    _ ≤ 2 ^ k * v := Nat.mul_le_mul_left _ hv

theorem dyadicDilates_disjoint {X : ℕ} {C : Finset ℕ}
    (hC : ∀ u ∈ C, X ≤ u ∧ u < 2 * X) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (dyadicDilate j C) (dyadicDilate k C) := by
  apply Finset.disjoint_left.mpr
  intro x hxj hxk
  obtain ⟨u, hu, hju⟩ := Finset.mem_image.mp hxj
  obtain ⟨v, hv, hkv⟩ := Finset.mem_image.mp hxk
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · exact (ne_of_lt (dyadic_scaled_lt (hC u hu).2 (hC v hv).1 hjk))
      (hju.trans hkv.symm)
  · exact (ne_of_lt (dyadic_scaled_lt (hC v hv).2 (hC u hu).1 hkj))
      (hkv.trans hju.symm)

theorem dyadicDilate_card (j : ℕ) (C : Finset ℕ) :
    (dyadicDilate j C).card = C.card := by
  apply Finset.card_image_of_injective
  intro u v huv
  exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos j) huv

theorem layeredHost_card {X L : ℕ} {C : Finset ℕ}
    (hC : ∀ u ∈ C, X ≤ u ∧ u < 2 * X) :
    (layeredHost L C).card = L * C.card := by
  have hdisjoint : (Finset.range L : Set ℕ).PairwiseDisjoint
      (fun j => dyadicDilate j C) := by
    intro j _ k _ hjk
    exact dyadicDilates_disjoint hC hjk
  rw [layeredHost, Finset.card_biUnion hdisjoint]
  simp only [dyadicDilate_card, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]

theorem selected_layer_card_sum {X L : ℕ} {C B : Finset ℕ}
    (hC : ∀ u ∈ C, X ≤ u ∧ u < 2 * X) (hB : B ⊆ layeredHost L C) :
    B.card = ∑ j ∈ Finset.range L, (levelSlice j C B).card := by
  let P := fun j => dyadicDilate j (levelSlice j C B)
  have heq : B = (Finset.range L).biUnion P := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp (hB hx)
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxj
      exact Finset.mem_biUnion.mpr ⟨j, hj,
        Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hx⟩, rfl⟩⟩
    · intro hx
      obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxj
      exact (Finset.mem_filter.mp hu).2
  have hdisjoint : (Finset.range L : Set ℕ).PairwiseDisjoint P := by
    intro j _ k _ hjk
    exact (dyadicDilates_disjoint hC hjk).mono
      (Finset.image_subset_image (Finset.filter_subset _ _))
      (Finset.image_subset_image (Finset.filter_subset _ _))
  calc
    B.card = ((Finset.range L).biUnion P).card := congrArg Finset.card heq
    _ = ∑ j ∈ Finset.range L, (P j).card := Finset.card_biUnion hdisjoint
    _ = ∑ j ∈ Finset.range L, (levelSlice j C B).card := by
      apply Finset.sum_congr rfl
      intro j _
      exact dyadicDilate_card _ _

theorem light_level_mass_le (L K : ℕ) (C B : Finset ℕ) :
    (∑ j ∈ (Finset.range L).filter (fun j => (levelSlice j C B).card < K),
      (levelSlice j C B).card) ≤ L * K := by
  calc
    (∑ j ∈ (Finset.range L).filter (fun j => (levelSlice j C B).card < K),
        (levelSlice j C B).card) ≤
        ∑ _j ∈ (Finset.range L).filter (fun j => (levelSlice j C B).card < K), K := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Finset.mem_filter.mp hj).2.le
    _ = ((Finset.range L).filter (fun j => (levelSlice j C B).card < K)).card * K := by
      simp
    _ ≤ L * K := Nat.mul_le_mul_right K
      ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range L))

end Erdos790.Upper
