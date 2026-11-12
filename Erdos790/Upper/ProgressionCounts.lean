import Erdos790.Upper.CenterCapacity

/-!
# Exact midpoint-triple counts

A pair `(x, z)` encodes the ordered triple `(x, z, 2*z-x)`. The count includes
the trivial triples. This matches the convention in the progression-count
estimate used by the distinct-summand lift.
-/

open Finset

namespace Erdos790.Upper

def progressionPairs (S : Finset ℤ) : Finset (ℤ × ℤ) :=
  (S ×ˢ S).filter fun p => 2 * p.2 - p.1 ∈ S

theorem endpoint_count {S : Finset ℤ} {z : ℤ} (hz : z ∈ S) :
    (S.filter fun x => 2 * z - x ∈ S).card =
      2 * (lowerPairEndpoints S z).card + 1 := by
  let T := lowerPairEndpoints S z
  have hT : ∀ x ∈ T, x < z := fun _ hx => (Finset.mem_filter.mp hx).2.1
  have heq : S.filter (fun x => 2 * z - x ∈ S) =
      insert z (T ∪ T.image fun x => 2 * z - x) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxS, hrS⟩ := Finset.mem_filter.mp hx
      rcases lt_trichotomy x z with hxz | rfl | hzx
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hxS, hxz, hrS⟩))
      · exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨2 * z - x, ?_, by omega⟩
        apply Finset.mem_filter.mpr
        refine ⟨hrS, by omega, ?_⟩
        have hreflect : 2 * z - (2 * z - x) = x := by omega
        simpa only [hreflect] using hxS
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr
          ⟨hz, by simpa only [two_mul, add_sub_cancel_right] using hz⟩
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxS, _, hrS⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hxS, hrS⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨hyS, _, hrS⟩ := Finset.mem_filter.mp hy
        apply Finset.mem_filter.mpr
        refine ⟨hrS, ?_⟩
        have hreflect : 2 * z - (2 * z - y) = y := by omega
        simpa only [hreflect] using hyS
  have hzT : z ∉ T ∪ T.image (fun x => 2 * z - x) := by
    simp only [Finset.mem_union, not_or]
    exact ⟨center_not_mem_lower hT, center_not_mem_reflection hT⟩
  rw [heq, Finset.card_insert_of_notMem hzT, centered_endpoints_card hT]

theorem progressionPairs_card (S : Finset ℤ) :
    (progressionPairs S).card =
      S.card + 2 * ∑ z ∈ S, (lowerPairEndpoints S z).card := by
  have hbycenter : (progressionPairs S).card =
      ∑ z ∈ S, (S.filter fun x => 2 * z - x ∈ S).card := by
    unfold progressionPairs
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
    rw [Finset.sum_comm]
  rw [hbycenter]
  calc
    (∑ z ∈ S, (S.filter fun x => 2 * z - x ∈ S).card) =
        ∑ z ∈ S, (2 * (lowerPairEndpoints S z).card + 1) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact endpoint_count hz
    _ = S.card + 2 * ∑ z ∈ S, (lowerPairEndpoints S z).card := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        smul_eq_mul, mul_one]
      omega

theorem progressionPairs_card_le_of_no_good {R : ℕ} {S : Finset ℤ}
    (hbad : ∀ z, ¬GoodCenter R S z) :
    (progressionPairs S).card ≤ (R + 1) * S.card := by
  have hlocal : ∀ z ∈ S, (S.filter fun x => 2 * z - x ∈ S).card ≤ R + 1 := by
    intro z hz
    rw [endpoint_count hz]
    have hlt : (lowerPairEndpoints S z).card < R / 2 := by
      by_contra h
      exact hbad z ⟨hz, by omega⟩
    omega
  have hbycenter : (progressionPairs S).card =
      ∑ z ∈ S, (S.filter fun x => 2 * z - x ∈ S).card := by
    unfold progressionPairs
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
    rw [Finset.sum_comm]
  rw [hbycenter]
  calc
    (∑ z ∈ S, (S.filter fun x => 2 * z - x ∈ S).card) ≤ ∑ _z ∈ S, (R + 1) :=
      Finset.sum_le_sum hlocal
    _ = (R + 1) * S.card := by simp [Nat.mul_comm]

theorem centerRich_of_progression_count {R K : ℕ} {D : Finset ℤ}
    (hcount : ∀ S ⊆ D, K < S.card → (R + 1) * S.card < (progressionPairs S).card) :
    CenterRich R K D := by
  intro S hSD hK
  by_contra h
  push Not at h
  exact (not_lt_of_ge (progressionPairs_card_le_of_no_good h)) (hcount S hSD hK)

end Erdos790.Upper
