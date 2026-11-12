import Erdos790.Upper.CenteredPairs

/-!
# Lifting repeated coarse relations to distinct integer relations

The finite argument uses centered pairs to realize each multiplicity and
disjoint affine fibers to preserve distinctness.
-/

open Finset

namespace Erdos790.Upper

/-- A positive relation with at least two terms cannot use its head as a term. -/
theorem positive_relation_head_zero {F : Finset ℕ} {a : ℕ}
    (hpos : ∀ b ∈ F, 0 < b) (ha : a ∈ F) (multiplicity : ℕ → ℕ)
    (hlength : 2 ≤ ∑ b ∈ F, multiplicity b)
    (hsum : ∑ b ∈ F, multiplicity b * b = a) : multiplicity a = 0 := by
  have ha_pos := hpos a ha
  have hcount := Finset.sum_erase_add F multiplicity ha
  have hweight := Finset.sum_erase_add F (fun b => multiplicity b * b) ha
  have hrest : (∑ b ∈ F.erase a, multiplicity b) ≤
      ∑ b ∈ F.erase a, multiplicity b * b := by
    apply Finset.sum_le_sum
    intro b hb
    exact Nat.le_mul_of_pos_right _ (hpos b (Finset.mem_of_mem_erase hb))
  by_contra hnonzero
  by_cases hone : multiplicity a = 1
  · rw [hone, one_mul, hsum] at hweight
    rw [hone] at hcount
    omega
  · have htwo : 2 ≤ multiplicity a := by omega
    have hlarge := Nat.mul_le_mul_right a htwo
    omega

/-- The integer in the fiber over `a` with digit `u`. -/
def liftValue (H : ℤ) (a : ℕ) (u : ℤ) : ℤ := (a : ℤ) * (H + u)

def selectedDigits (H : ℤ) (a : ℕ) (B D : Finset ℤ) : Finset ℤ :=
  D.filter fun u => liftValue H a u ∈ B

noncomputable def goodLabels (R : ℕ) (H v : ℤ) (F : Finset ℕ)
    (B D : Finset ℤ) : Finset ℕ := by
  classical
  exact F.filter fun a => GoodCenter R (selectedDigits H a B D) v

def FiberSeparated (H : ℤ) (F : Finset ℕ) (D : Finset ℤ) : Prop :=
  ∀ a ∈ F, ∀ u ∈ D, ∀ b ∈ F, ∀ v ∈ D,
    liftValue H a u = liftValue H b v → a = b ∧ u = v

theorem liftValue_injective {H : ℤ} {a : ℕ} (ha : 0 < a) :
    Function.Injective (liftValue H a) := by
  intro u v h
  have hne : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hsum : H + u = H + v := mul_left_cancel₀ hne h
  omega

theorem sum_liftValue (H : ℤ) (a : ℕ) (T : Finset ℤ) :
    ∑ u ∈ T, liftValue H a u = (a : ℤ) * ((T.card : ℤ) * H + ∑ u ∈ T, u) := by
  simp only [liftValue, mul_add, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Good labels in separated fibers inherit the repeated-sum restriction. -/
theorem goodLabels_repeatedSumFree {R : ℕ} {H v : ℤ} {F : Finset ℕ}
    {B D : Finset ℤ} (hpos : ∀ a ∈ F, 0 < a)
    (hsep : FiberSeparated H F D) (hB : Erdos790.IsSumFree B) :
    RepeatedSumFree R (goodLabels R H v F B D) := by
  classical
  let C := goodLabels R H v F B D
  have hCF : C ⊆ F := Finset.filter_subset _ _
  have hCpos : ∀ a ∈ C, 0 < a := fun a ha => hpos a (hCF ha)
  change RepeatedSumFree R C
  intro a ha multiplicity hlower hupper hrelation
  have hzero := positive_relation_head_zero hCpos ha multiplicity hlower hrelation
  have hexists : ∀ b : ℕ, ∃ T : Finset ℤ, b ∈ C →
      T ⊆ selectedDigits H b B D ∧ T.card = multiplicity b ∧
        ∑ u ∈ T, u = (multiplicity b : ℤ) * v := by
    intro b
    by_cases hb : b ∈ C
    · have hgood : GoodCenter R (selectedDigits H b B D) v :=
        (Finset.mem_filter.mp hb).2
      have hle : multiplicity b ≤ R :=
        (Finset.single_le_sum (fun c _ => Nat.zero_le (multiplicity c)) hb).trans hupper
      obtain ⟨T, hTS, hcard, hsum⟩ := hgood.realize_multiplicity hle
      exact ⟨T, fun _ => ⟨hTS, hcard, hsum⟩⟩
    · exact ⟨∅, fun h => (hb h).elim⟩
  choose T hT using hexists
  let P : ℕ → Finset ℤ := fun b => (T b).image (liftValue H b)
  have hTD : ∀ b ∈ C, T b ⊆ D := by
    intro b hb u hu
    exact (Finset.mem_filter.mp ((hT b hb).1 hu)).1
  have hPB : ∀ b ∈ C, P b ⊆ B := by
    intro b hb x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp ((hT b hb).1 hu)).2
  have hdisjoint : (C : Set ℕ).PairwiseDisjoint P := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro x hxb hxc
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxb
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hxc
    exact hbc (hsep b (hCF hb) u (hTD b hb hu) c (hCF hc) w (hTD c hc hw) heq.symm).1
  have hPcard : ∀ b ∈ C, (P b).card = multiplicity b := by
    intro b hb
    exact (Finset.card_image_of_injective _ (liftValue_injective (hCpos b hb))).trans
      (hT b hb).2.1
  have hPsum : ∀ b ∈ C,
      ∑ x ∈ P b, x = (multiplicity b : ℤ) * liftValue H b v := by
    intro b hb
    change ∑ x ∈ (T b).image (liftValue H b), x = _
    rw [Finset.sum_image (fun x _ y _ h => liftValue_injective (hCpos b hb) h),
      sum_liftValue, (hT b hb).2.1, (hT b hb).2.2]
    simp only [liftValue]
    ring
  let Q := C.biUnion P
  have hQB : Q ⊆ B := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
    exact hPB b hb hxb
  have hgoodA : GoodCenter R (selectedDigits H a B D) v :=
    (Finset.mem_filter.mp ha).2
  have hvD : v ∈ D := (Finset.mem_filter.mp hgoodA.1).1
  have hheadB : liftValue H a v ∈ B := (Finset.mem_filter.mp hgoodA.1).2
  have hheadQ : liftValue H a v ∉ Q := by
    intro hx
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hxb
    have hba := (hsep b (hCF hb) u (hTD b hb hu) a (hCF ha) v hvD heq).1
    have hcardzero : (T b).card = 0 := by rw [(hT b hb).2.1, hba, hzero]
    have hempty := Finset.card_eq_zero.mp hcardzero
    simp only [hempty, Finset.notMem_empty] at hu
  have hQerase : Q ⊆ B.erase (liftValue H a v) := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun heq => hheadQ (heq ▸ hx), hQB hx⟩
  have hQcard : Q.card = ∑ b ∈ C, multiplicity b := by
    rw [Finset.card_biUnion hdisjoint]
    exact Finset.sum_congr rfl hPcard
  have hQsum : ∑ x ∈ Q, x = liftValue H a v := by
    calc
      ∑ x ∈ Q, x = ∑ b ∈ C, (multiplicity b : ℤ) * liftValue H b v := by
        rw [Finset.sum_biUnion hdisjoint]
        exact Finset.sum_congr rfl hPsum
      _ = (∑ b ∈ C, (multiplicity b : ℤ) * (b : ℤ)) * (H + v) := by
        simp only [liftValue, ← mul_assoc, Finset.sum_mul]
      _ = liftValue H a v := by
        unfold liftValue
        congr 1
        exact_mod_cast hrelation
  exact hB (liftValue H a v) hheadB Q hQerase (hQcard ▸ hlower) hQsum

end Erdos790.Upper
