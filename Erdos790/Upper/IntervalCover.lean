import Erdos790.Upper.MidpointCounting
import Mathlib.Data.Int.Interval

/-!
# Integer intervals inside the propagated mixed means

The invariant records a sufficiently long interval through every attained
point. It is preserved, with the length halved, by one midpoint step.
-/

open Finset

namespace Erdos790.Upper

def IntervalCovered (m : ℕ) (T : Finset ℤ) : Prop :=
  ∀ x ∈ T, ∃ a b : ℤ,
    a ≤ x ∧ x ≤ b ∧ (m : ℤ) ≤ b - a + 1 ∧ Finset.Icc a b ⊆ T

theorem IntervalCovered.midpointClosure {m : ℕ} {T S : Finset ℤ}
    (hT : IntervalCovered m T) : IntervalCovered (m / 2) (midpointClosure T S) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxT | hxMid
  · obtain ⟨a, b, ha, hb, hlength, hsubset⟩ := hT x hxT
    refine ⟨a, b, ha, hb, ?_, hsubset.trans (Finset.subset_union_left)⟩
    have hm : (m / 2 : ℕ) ≤ m := Nat.div_le_self _ _
    omega
  · obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hxMid
    obtain ⟨hxy, heven⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hxT, hyS⟩ := Finset.mem_product.mp hxy
    obtain ⟨a, b, ha, hb, hlength, hsubset⟩ := hT xy.1 hxT
    let lower := (a + xy.2 + 1) / 2
    let upper := (b + xy.2) / 2
    refine ⟨lower, upper, ?_, ?_, ?_, ?_⟩
    · dsimp [lower]
      omega
    · dsimp [upper]
      omega
    · dsimp [lower, upper]
      omega
    · intro z hz
      obtain ⟨hlower, hupper⟩ := Finset.mem_Icc.mp hz
      have hpreimage : 2 * z - xy.2 ∈ T := by
        apply hsubset
        apply Finset.mem_Icc.mpr
        dsimp [lower, upper] at hlower hupper
        omega
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(2 * z - xy.2, xy.2), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hpreimage, hyS⟩, by omega⟩
      · dsimp
        omega

def rightEnds (T : Finset ℤ) : Finset ℤ := T.filter fun p => p + 1 ∉ T

theorem rightEnd_block_subset {m : ℕ} {T : Finset ℤ}
    (hT : IntervalCovered m T) {p : ℤ} (hp : p ∈ rightEnds T) :
    Finset.Icc (p - m + 1) p ⊆ T := by
  obtain ⟨hpT, hpnext⟩ := Finset.mem_filter.mp hp
  obtain ⟨a, b, ha, hb, hlength, hsubset⟩ := hT p hpT
  have hb_le : b ≤ p := by
    by_contra h
    have hnext : p + 1 ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact hpnext (hsubset hnext)
  intro x hx
  obtain ⟨hleft, hright⟩ := Finset.mem_Icc.mp hx
  exact hsubset (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

theorem rightEnd_blocks_disjoint {m : ℕ} {T : Finset ℤ}
    (hT : IntervalCovered m T) : (rightEnds T : Set ℤ).PairwiseDisjoint
      (fun p => Finset.Icc (p - m + 1) p) := by
  intro p hp q hq hpq
  apply Finset.disjoint_left.mpr
  intro x hxp hxq
  obtain ⟨hpl, hpr⟩ := Finset.mem_Icc.mp hxp
  obtain ⟨hql, hqr⟩ := Finset.mem_Icc.mp hxq
  rcases lt_or_gt_of_ne hpq with hpq | hqp
  · have hnext : p + 1 ∈ Finset.Icc (q - m + 1) q :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact (Finset.mem_filter.mp hp).2 (rightEnd_block_subset hT hq hnext)
  · have hnext : q + 1 ∈ Finset.Icc (p - m + 1) p :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact (Finset.mem_filter.mp hq).2 (rightEnd_block_subset hT hp hnext)

theorem rightEnds_card_mul_le {m : ℕ} {T : Finset ℤ}
    (hT : IntervalCovered m T) : (rightEnds T).card * m ≤ T.card := by
  have hblock_card : ∀ p : ℤ, (Finset.Icc (p - m + 1) p).card = m := by
    intro p
    rw [Int.card_Icc]
    omega
  calc
    (rightEnds T).card * m = ∑ _p ∈ rightEnds T, m := by simp
    _ = ∑ p ∈ rightEnds T, (Finset.Icc (p - m + 1) p).card := by
      simp only [hblock_card]
    _ = ((rightEnds T).biUnion fun p => Finset.Icc (p - m + 1) p).card :=
      (Finset.card_biUnion (rightEnd_blocks_disjoint hT)).symm
    _ ≤ T.card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
      exact rightEnd_block_subset hT hp hxp

theorem rightEnd_previous_mem {m : ℕ} {T : Finset ℤ} (hT : IntervalCovered m T)
    (hm : 2 ≤ m) {p : ℤ} (hp : p ∈ rightEnds T) : p - 1 ∈ T :=
  rightEnd_block_subset hT hp (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

theorem minimum_next_mem {m : ℕ} {T : Finset ℤ} (hT : IntervalCovered m T)
    (hm : 2 ≤ m) {p : ℤ} (hp : p ∈ T) (hmin : ∀ x ∈ T, p ≤ x) : p + 1 ∈ T := by
  obtain ⟨a, b, ha, hb, hlength, hsubset⟩ := hT p hp
  have haT : a ∈ T := hsubset (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hpa := hmin a haT
  exact hsubset (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

end Erdos790.Upper
