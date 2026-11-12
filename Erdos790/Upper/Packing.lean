import Erdos790.Upper.Basic

/-!
# Packing positive witnesses to obtain every host size

Disjoint integer dilates preserve the restriction on distinct sums. This file
proves the exact quotient-and-remainder bound for arbitrary target sizes.
-/

open Finset

namespace Erdos790.Upper

def IndependentBound (A : Finset ℤ) (m : ℕ) : Prop :=
  ∀ B ⊆ A, Erdos790.IsSumFree B → B.card ≤ m

theorem IndependentBound.union {A C : Finset ℤ} {m k : ℕ}
    (hA : IndependentBound A m) (hC : IndependentBound C k) :
    IndependentBound (A ∪ C) (m + k) := by
  intro B hB hfree
  have heq : B = (B ∩ A) ∪ (B ∩ C) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp (hB hx) with hxA | hxC
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxC⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxA | hxC
      · exact (Finset.mem_inter.mp hxA).1
      · exact (Finset.mem_inter.mp hxC).1
  calc
    B.card = ((B ∩ A) ∪ (B ∩ C)).card := congrArg Finset.card heq
    _ ≤ (B ∩ A).card + (B ∩ C).card := Finset.card_union_le _ _
    _ ≤ m + k := Nat.add_le_add
      (hA _ Finset.inter_subset_right (hfree.mono Finset.inter_subset_left))
      (hC _ Finset.inter_subset_right (hfree.mono Finset.inter_subset_left))

theorem isSumFree_of_image_mul {A : Finset ℤ} {c : ℤ} (hc : c ≠ 0)
    (hA : Erdos790.IsSumFree (A.image fun x => c * x)) : Erdos790.IsSumFree A := by
  intro b hb S hS hcard hsum
  have hinj : Function.Injective (fun x : ℤ => c * x) :=
    fun _ _ h => mul_left_cancel₀ hc h
  have himage : S.image (fun x => c * x) ⊆
      (A.image fun x => c * x).erase (c * b) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hyA := Finset.mem_erase.mp (hS hy)
    exact Finset.mem_erase.mpr
      ⟨fun h => hyA.1 (hinj h), Finset.mem_image.mpr ⟨y, hyA.2, rfl⟩⟩
  have hcardimage : 2 ≤ (S.image fun x => c * x).card := by
    rwa [Finset.card_image_of_injective _ hinj]
  apply hA (c * b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    (S.image fun x => c * x) himage hcardimage
  rw [Finset.sum_image (fun x _ y _ h => hinj h), ← Finset.mul_sum, hsum]

theorem IndependentBound.image_mul {A : Finset ℤ} {m : ℕ} {c : ℤ}
    (hA : IndependentBound A m) (hc : c ≠ 0) :
    IndependentBound (A.image fun x => c * x) m := by
  classical
  intro B hB hfree
  let T := A.filter fun x => c * x ∈ B
  have heq : T.image (fun x => c * x) = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      obtain ⟨y, hyA, rfl⟩ := Finset.mem_image.mp (hB hx)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hyA, hx⟩, rfl⟩
  have hTfree : Erdos790.IsSumFree T := by
    apply isSumFree_of_image_mul hc
    rwa [heq]
  have hTcard := hA T (Finset.filter_subset _ _) hTfree
  have hinj : Function.Injective (fun x : ℤ => c * x) :=
    fun _ _ h => mul_left_cancel₀ hc h
  rw [← heq, Finset.card_image_of_injective _ hinj]
  exact hTcard

theorem exists_positive_above (F : Finset ℤ) :
    ∃ c : ℤ, 0 < c ∧ ∀ x ∈ F, x < c := by
  let c := (∑ x ∈ F, |x|) + 1
  have hsum : (0 : ℤ) ≤ ∑ x ∈ F, |x| :=
    Finset.sum_nonneg (fun x _ => abs_nonneg x)
  refine ⟨c, by dsimp [c]; omega, ?_⟩
  intro x hx
  have habs : |x| ≤ ∑ y ∈ F, |y| :=
    Finset.single_le_sum (fun y _ => abs_nonneg y) hx
  have hxabs := le_abs_self x
  dsimp [c]
  omega

theorem exists_disjoint_positive_dilate (F A : Finset ℤ)
    (hA : ∀ a ∈ A, 0 < a) :
    ∃ c : ℤ, 0 < c ∧ Disjoint F (A.image fun a => c * a) := by
  obtain ⟨c, hc, habove⟩ := exists_positive_above F
  refine ⟨c, hc, Finset.disjoint_left.mpr ?_⟩
  intro x hxF hxA
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxA
  have ha_one : 1 ≤ a := hA a ha
  have hca : c ≤ c * a := by nlinarith
  exact (not_lt_of_ge hca) (habove (c * a) hxF)

theorem IndependentBound.positive_copies {A : Finset ℤ} {m : ℕ}
    (hA : IndependentBound A m) (hpositive : ∀ a ∈ A, 0 < a) (k : ℕ) :
    ∃ F : Finset ℤ, (∀ x ∈ F, 0 < x) ∧ F.card = k * A.card ∧
      IndependentBound F (k * m) := by
  classical
  induction k with
  | zero =>
    refine ⟨∅, by simp, by simp, ?_⟩
    intro B hB _
    have hBempty : B = ∅ := Finset.subset_empty.mp hB
    simp [hBempty]
  | succ k ih =>
    obtain ⟨F, hFpositive, hFcard, hFbound⟩ := ih
    obtain ⟨c, hc, hdisjoint⟩ := exists_disjoint_positive_dilate F A hpositive
    let D := A.image fun a => c * a
    have hDpositive : ∀ x ∈ D, 0 < x := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact mul_pos hc (hpositive a ha)
    have hinj : Function.Injective (fun a : ℤ => c * a) :=
      fun _ _ h => mul_left_cancel₀ (ne_of_gt hc) h
    have hDcard : D.card = A.card := Finset.card_image_of_injective _ hinj
    have hDbound : IndependentBound D m := hA.image_mul (ne_of_gt hc)
    refine ⟨F ∪ D, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hxF | hxD
      · exact hFpositive x hxF
      · exact hDpositive x hxD
    · rw [Finset.card_union_of_disjoint hdisjoint, hFcard, hDcard]
      ring
    · simpa only [Nat.succ_mul] using hFbound.union hDbound

theorem IndependentBound.pad_positive {F : Finset ℤ} {m : ℕ}
    (hF : IndependentBound F m) (hpositive : ∀ x ∈ F, 0 < x) (r : ℕ) :
    ∃ A : Finset ℤ, (∀ x ∈ A, 0 < x) ∧ A.card = F.card + r ∧
      IndependentBound A (m + r) := by
  classical
  induction r with
  | zero => exact ⟨F, hpositive, by simp, by simpa using hF⟩
  | succ r ih =>
    obtain ⟨A, hApositive, hAcard, hAbound⟩ := ih
    obtain ⟨c, hc, habove⟩ := exists_positive_above A
    have hcA : c ∉ A := fun h => lt_irrefl c (habove c h)
    have hsingleton : IndependentBound ({c} : Finset ℤ) 1 := by
      intro B hB _
      exact (Finset.card_le_card hB).trans (by simp)
    refine ⟨A ∪ {c}, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hxA | hxc
      · exact hApositive x hxA
      · simpa only [Finset.mem_singleton.mp hxc] using hc
    · rw [Finset.union_singleton, Finset.card_insert_of_notMem hcA, hAcard]
      omega
    · simpa only [Nat.add_assoc, Nat.add_comm r 1] using hAbound.union hsingleton

/-- Every positive witness gives an exact bound at every target cardinality. -/
theorem IndependentBound.all_sizes {A : Finset ℤ} {m : ℕ}
    (hA : IndependentBound A m) (hpositive : ∀ a ∈ A, 0 < a)
    (n : ℕ) :
    Erdos790.UpperWitness n ((n / A.card * m + n % A.card : ℕ) : ℝ) := by
  obtain ⟨F, hFpositive, hFcard, hFbound⟩ := hA.positive_copies hpositive (n / A.card)
  obtain ⟨B, _, hBcard, hBbound⟩ := hFbound.pad_positive hFpositive (n % A.card)
  refine ⟨B, ?_, ?_⟩
  · rw [hBcard, hFcard]
    simpa only [Nat.mul_comm] using Nat.div_add_mod n A.card
  · intro S hSB hfree
    exact_mod_cast hBbound S hSB hfree

end Erdos790.Upper
