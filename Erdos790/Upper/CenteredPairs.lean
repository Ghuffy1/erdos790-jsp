import Erdos790.Upper.Basic

/-!
# Distinct digits with prescribed mean

This is the finite combinatorial step converting repeated coarse summands into
distinct lifted summands in the upper-bound construction.
-/

open Finset

namespace Erdos790.Upper

/-- Lower endpoints of nontrivial centered pairs in `S`. -/
def lowerPairEndpoints (S : Finset ℤ) (v : ℤ) : Finset ℤ :=
  S.filter fun x => x < v ∧ 2 * v - x ∈ S

/-- A selected center with sufficiently many distinct centered pairs. -/
def GoodCenter (R : ℕ) (S : Finset ℤ) (v : ℤ) : Prop :=
  v ∈ S ∧ R / 2 ≤ (lowerPairEndpoints S v).card

theorem centered_pair_sum (v x : ℤ) : x + (2 * v - x) = 2 * v := by
  ring

theorem reflect_center_injective (v : ℤ) :
    Function.Injective (fun x : ℤ => 2 * v - x) := by
  intro x y h
  change 2 * v - x = 2 * v - y at h
  omega

theorem lower_reflection_disjoint {v : ℤ} {T : Finset ℤ}
    (hT : ∀ x ∈ T, x < v) : Disjoint T (T.image fun x => 2 * v - x) := by
  rw [Finset.disjoint_left]
  intro x hx hximage
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hximage
  have hxl := hT x hx
  have hyl := hT y hy
  omega

theorem center_not_mem_lower {v : ℤ} {T : Finset ℤ}
    (hT : ∀ x ∈ T, x < v) : v ∉ T := by
  intro hv
  exact lt_irrefl v (hT v hv)

theorem center_not_mem_reflection {v : ℤ} {T : Finset ℤ}
    (hT : ∀ x ∈ T, x < v) : v ∉ T.image (fun x => 2 * v - x) := by
  intro hv
  obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hv
  have hxl := hT x hx
  omega

/-- Every finite family of centered pairs has twice as many distinct endpoints. -/
theorem centered_endpoints_card {v : ℤ} {T : Finset ℤ}
    (hT : ∀ x ∈ T, x < v) :
    (T ∪ T.image (fun x => 2 * v - x)).card = 2 * T.card := by
  rw [Finset.card_union_of_disjoint (lower_reflection_disjoint hT),
    Finset.card_image_of_injective _ (reflect_center_injective v)]
  omega

/-- The sum of all endpoints is their cardinality times their center. -/
theorem centered_endpoints_sum {v : ℤ} {T : Finset ℤ}
    (hT : ∀ x ∈ T, x < v) :
    ∑ x ∈ T ∪ T.image (fun x => 2 * v - x), x = (2 * T.card : ℕ) * v := by
  rw [Finset.sum_union (lower_reflection_disjoint hT),
    Finset.sum_image (fun x _ y _ h => reflect_center_injective v h)]
  rw [← Finset.sum_add_distrib]
  simp only [centered_pair_sum, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- A good center realizes every permitted multiplicity using distinct digits. -/
theorem GoodCenter.realize_multiplicity {R m : ℕ} {S : Finset ℤ} {v : ℤ}
    (hv : GoodCenter R S v) (hm : m ≤ R) :
    ∃ T ⊆ S, T.card = m ∧ ∑ x ∈ T, x = (m : ℤ) * v := by
  classical
  have hm2 : m / 2 ≤ (lowerPairEndpoints S v).card := by
    have hR := hv.2
    omega
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hm2
  have hlower : ∀ x ∈ T, x < v := by
    intro x hx
    exact (Finset.mem_filter.mp (hT hx)).2.1
  let P := T ∪ T.image (fun x => 2 * v - x)
  have hPS : P ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp (hT hx)).1
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp (hT hy)).2.2
  have hvP : v ∉ P := by
    simp only [P, Finset.mem_union, not_or]
    exact ⟨center_not_mem_lower hlower, center_not_mem_reflection hlower⟩
  have hPcard : P.card = 2 * (m / 2) := by
    simpa only [P, hcard] using centered_endpoints_card hlower
  have hPsum : ∑ x ∈ P, x = (2 * (m / 2) : ℕ) * v := by
    simpa only [P, hcard] using centered_endpoints_sum hlower
  by_cases heven : m % 2 = 0
  · have hm_eq : 2 * (m / 2) = m := by omega
    exact ⟨P, hPS, hPcard.trans hm_eq, by simpa only [hm_eq] using hPsum⟩
  · have hm_eq : m = 2 * (m / 2) + 1 := by omega
    refine ⟨insert v P, Finset.insert_subset hv.1 hPS, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hvP, hPcard]
      omega
    · rw [Finset.sum_insert hvP, hPsum]
      conv_rhs => rw [hm_eq]
      push_cast
      ring

end Erdos790.Upper
