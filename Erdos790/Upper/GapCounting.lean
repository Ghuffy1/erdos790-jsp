import Erdos790.Upper.IntervalCover
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Partitioning selected points into gaps

The optional tag records the last attained point to the left. The `none` tag
records the gap before all attained points.
-/

open Finset

namespace Erdos790.Upper

noncomputable def gapTag (T : Finset ℤ) (x : ℤ) : Option ℤ := by
  classical
  exact if h : (T.filter fun t => t < x).Nonempty then
    some ((T.filter fun t => t < x).max' h) else none

def gapTags (T : Finset ℤ) : Finset (Option ℤ) :=
  insert none ((rightEnds T).image some)

def InGap (T : Finset ℤ) (tag : Option ℤ) (x : ℤ) : Prop :=
  match tag with
  | none => ∀ t ∈ T, x < t
  | some p => p < x ∧ ∀ t ∈ T, p < t → x < t

theorem some_mem_gapTags {T : Finset ℤ} {p : ℤ} :
    some p ∈ gapTags T ↔ p ∈ rightEnds T := by
  simp [gapTags]

theorem gapTag_spec {T : Finset ℤ} {x : ℤ} (hx : x ∉ T) :
    gapTag T x ∈ gapTags T ∧ InGap T (gapTag T x) x := by
  classical
  unfold gapTag
  split
  · rename_i hnonempty
    let P := T.filter fun t => t < x
    let p := P.max' hnonempty
    have hpP : p ∈ P := Finset.max'_mem _ _
    have hpT : p ∈ T := (Finset.mem_filter.mp hpP).1
    have hpx : p < x := (Finset.mem_filter.mp hpP).2
    have hgap : ∀ t ∈ T, p < t → x < t := by
      intro t ht hpt
      by_contra hxt
      have hne : t ≠ x := fun heq => hx (heq ▸ ht)
      have htx : t < x := by omega
      have htP : t ∈ P := Finset.mem_filter.mpr ⟨ht, htx⟩
      have htp : t ≤ p := Finset.le_max' P t htP
      omega
    have hpEnd : p ∈ rightEnds T := by
      apply Finset.mem_filter.mpr
      refine ⟨hpT, ?_⟩
      intro hpnext
      have h := hgap (p + 1) hpnext (by omega)
      omega
    exact ⟨some_mem_gapTags.mpr hpEnd, hpx, hgap⟩
  · rename_i hempty
    refine ⟨Finset.mem_insert_self _ _, ?_⟩
    intro t ht
    by_contra hxt
    have hne : t ≠ x := fun heq => hx (heq ▸ ht)
    have htx : t < x := by omega
    exact hempty ⟨t, Finset.mem_filter.mpr ⟨ht, htx⟩⟩

theorem InGap.not_mem {T : Finset ℤ} {tag : Option ℤ} {x : ℤ}
    (h : InGap T tag x) : x ∉ T := by
  intro hx
  cases tag with
  | none => exact lt_irrefl x (h x hx)
  | some p => exact lt_irrefl x (h.2 x hx h.1)

theorem InGap.unique_tag {T : Finset ℤ} {a b : Option ℤ} {x : ℤ}
    (ha : a ∈ gapTags T) (hb : b ∈ gapTags T)
    (hxa : InGap T a x) (hxb : InGap T b x) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some q =>
      have hqT := (Finset.mem_filter.mp (some_mem_gapTags.mp hb)).1
      have hlt := hxa q hqT
      have hgt := hxb.1
      omega
  | some p =>
    have hpT := (Finset.mem_filter.mp (some_mem_gapTags.mp ha)).1
    cases b with
    | none =>
      have hlt := hxb p hpT
      have hgt := hxa.1
      omega
    | some q =>
      have hqT := (Finset.mem_filter.mp (some_mem_gapTags.mp hb)).1
      rcases lt_trichotomy p q with hpq | hpq | hqp
      · have hlt := hxa.2 q hqT hpq
        have hgt := hxb.1
        omega
      · exact congrArg some hpq
      · have hlt := hxb.2 p hpT hqp
        have hgt := hxa.1
        omega

noncomputable def gapSelection (T S : Finset ℤ) (tag : Option ℤ) : Finset ℤ :=
  S.filter fun x => gapTag T x = tag

theorem gapSelection_spec {T S : Finset ℤ} (hdisjoint : Disjoint T S)
    {tag : Option ℤ} {x : ℤ} (hx : x ∈ gapSelection T S tag) :
    x ∈ S ∧ InGap T tag x := by
  obtain ⟨hxS, htag⟩ := Finset.mem_filter.mp hx
  have hxT : x ∉ T := fun h => Finset.disjoint_left.mp hdisjoint h hxS
  have hgap := (gapTag_spec hxT).2
  rw [htag] at hgap
  exact ⟨hxS, hgap⟩

theorem gapTags_card (T : Finset ℤ) : (gapTags T).card = (rightEnds T).card + 1 := by
  unfold gapTags
  rw [Finset.card_insert_of_notMem (by simp)]
  rw [Finset.card_image_of_injective _ (fun _ _ h => Option.some.inj h)]

noncomputable def gapMidpoints (T S : Finset ℤ) (hT : T.Nonempty)
    (tag : Option ℤ) : Finset ℤ :=
  match tag with
  | none => ((gapSelection T S none).erase (T.min' hT - 1)).image
      (fun x => (x + T.min' hT + 1) / 2)
  | some p => ((gapSelection T S (some p)).erase (p + 1)).image
      (fun x => (x + p) / 2)

theorem gapMidpoints_count (T S : Finset ℤ) (hT : T.Nonempty) (tag : Option ℤ) :
    (gapSelection T S tag).card ≤ 2 * (gapMidpoints T S hT tag).card + 1 := by
  cases tag with
  | none =>
    simpa only [gapMidpoints, add_assoc] using
      erase_half_image_card (gapSelection T S none) (T.min' hT + 1) (T.min' hT - 1)
  | some p => exact erase_half_image_card (gapSelection T S (some p)) p (p + 1)

theorem gapMidpoints_spec {m : ℕ} {T S : Finset ℤ}
    (hT : T.Nonempty) (hcovered : IntervalCovered m T) (hm : 2 ≤ m)
    (hdisjoint : Disjoint T S) {tag : Option ℤ} (htag : tag ∈ gapTags T)
    {z : ℤ} (hz : z ∈ gapMidpoints T S hT tag) :
    z ∈ midpointClosure T S ∧ InGap T tag z := by
  cases tag with
  | none =>
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxSelection := Finset.mem_of_mem_erase hx
    obtain ⟨hxS, hxgap⟩ := gapSelection_spec hdisjoint hxSelection
    let p := T.min' hT
    have hpT : p ∈ T := Finset.min'_mem _ _
    have hmin : ∀ y ∈ T, p ≤ y := fun y hy => Finset.min'_le T y hy
    have hnext : p + 1 ∈ T := minimum_next_mem hcovered hm hpT hmin
    have hxp : x < p := hxgap p hpT
    have hxne : x ≠ p - 1 := (Finset.mem_erase.mp hx).1
    have hzp : (x + p + 1) / 2 < p := by omega
    refine ⟨boundary_ceil_mem_midpointClosure hpT hnext hxS, ?_⟩
    intro y hy
    exact hzp.trans_le (hmin y hy)
  | some p =>
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxSelection := Finset.mem_of_mem_erase hx
    obtain ⟨hxS, hxgap⟩ := gapSelection_spec hdisjoint hxSelection
    have hpEnd : p ∈ rightEnds T := some_mem_gapTags.mp htag
    have hpT : p ∈ T := (Finset.mem_filter.mp hpEnd).1
    have hprev : p - 1 ∈ T := rightEnd_previous_mem hcovered hm hpEnd
    have hxne : x ≠ p + 1 := (Finset.mem_erase.mp hx).1
    have hpx : p < x := hxgap.1
    have hpz : p < (x + p) / 2 := by omega
    have hzx : (x + p) / 2 < x := by omega
    refine ⟨boundary_half_mem_midpointClosure hpT hprev hxS, hpz, ?_⟩
    intro y hy hpy
    exact hzx.trans (hxgap.2 y hy hpy)

theorem midpoint_growth_bound {m : ℕ} {T S : Finset ℤ}
    (hT : T.Nonempty) (hcovered : IntervalCovered m T) (hm : 2 ≤ m)
    (hdisjoint : Disjoint T S) :
    S.card ≤ 2 * (midpointClosure T S \ T).card + (rightEnds T).card + 1 := by
  classical
  let N := gapMidpoints T S hT
  have hpartition : S.card = ∑ tag ∈ gapTags T, (gapSelection T S tag).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x hxS
    have hxT : x ∉ T := fun h => Finset.disjoint_left.mp hdisjoint h hxS
    exact (gapTag_spec hxT).1
  have hpairwise : (gapTags T : Set (Option ℤ)).PairwiseDisjoint N := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro z hza hzb
    have hsA := gapMidpoints_spec hT hcovered hm hdisjoint ha hza
    have hsB := gapMidpoints_spec hT hcovered hm hdisjoint hb hzb
    exact hab (InGap.unique_tag ha hb hsA.2 hsB.2)
  have hsum : (∑ tag ∈ gapTags T, (N tag).card) ≤ (midpointClosure T S \ T).card := by
    rw [← Finset.card_biUnion hpairwise]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨tag, htag, hzN⟩ := Finset.mem_biUnion.mp hz
    have hspec := gapMidpoints_spec hT hcovered hm hdisjoint htag hzN
    exact Finset.mem_sdiff.mpr ⟨hspec.1, hspec.2.not_mem⟩
  calc
    S.card = ∑ tag ∈ gapTags T, (gapSelection T S tag).card := hpartition
    _ ≤ ∑ tag ∈ gapTags T, (2 * (N tag).card + 1) :=
      Finset.sum_le_sum (fun tag _ => gapMidpoints_count T S hT tag)
    _ = 2 * (∑ tag ∈ gapTags T, (N tag).card) + (gapTags T).card := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Nat.nsmul_eq_mul, mul_one]
    _ ≤ 2 * (midpointClosure T S \ T).card + (gapTags T).card :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hsum) _
    _ = 2 * (midpointClosure T S \ T).card + (rightEnds T).card + 1 := by
      rw [gapTags_card]
      omega

end Erdos790.Upper
