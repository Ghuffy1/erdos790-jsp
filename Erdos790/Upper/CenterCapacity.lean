import Erdos790.Upper.Lifting

/-!
# Quantitative transfer through centered pairs

The center-richness hypothesis is the finite consequence supplied by the
quantitative arithmetic-progression theorem in the informal proof. It remains
an explicit hypothesis here.
-/

open Finset
open scoped Classical

namespace Erdos790.Upper

theorem lowerPairEndpoints_mono {S T : Finset ℤ} (hST : S ⊆ T) (v : ℤ) :
    lowerPairEndpoints S v ⊆ lowerPairEndpoints T v := by
  intro x hx
  obtain ⟨hxS, hlt, hreflect⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hST hxS, hlt, hST hreflect⟩

theorem GoodCenter.mono {R : ℕ} {S T : Finset ℤ} {v : ℤ}
    (hv : GoodCenter R S v) (hST : S ⊆ T) : GoodCenter R T v :=
  ⟨hST hv.1, hv.2.trans (Finset.card_le_card (lowerPairEndpoints_mono hST v))⟩

noncomputable def goodCenters (R : ℕ) (S : Finset ℤ) : Finset ℤ := by
  classical
  exact S.filter fun v => GoodCenter R S v

@[simp] theorem mem_goodCenters {R : ℕ} {S : Finset ℤ} {v : ℤ} :
    v ∈ goodCenters R S ↔ GoodCenter R S v := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · exact fun h => Finset.mem_filter.mpr ⟨h.1, h⟩

/-- Every digit subset larger than `K` contains a center with `R / 2` pairs. -/
def CenterRich (R K : ℕ) (D : Finset ℤ) : Prop :=
  ∀ S ⊆ D, K < S.card → ∃ v, GoodCenter R S v

theorem CenterRich.card_le {R K : ℕ} {D S : Finset ℤ}
    (hD : CenterRich R K D) (hSD : S ⊆ D) :
    S.card ≤ (goodCenters R S).card + K := by
  classical
  let bad := S.filter fun v => ¬GoodCenter R S v
  have hbad : bad.card ≤ K := by
    by_contra h
    obtain ⟨v, hv⟩ := hD bad ((Finset.filter_subset _ _).trans hSD) (by omega)
    have hvbad := (Finset.mem_filter.mp hv.1).2
    exact hvbad (hv.mono (Finset.filter_subset _ _))
  have hpartition := Finset.card_filter_add_card_filter_not (s := S)
    (fun v => GoodCenter R S v)
  change (goodCenters R S).card + bad.card = S.card at hpartition
  omega

theorem goodCenters_selected_eq_filter (R : ℕ) (H : ℤ) (a : ℕ) (B D : Finset ℤ) :
    goodCenters R (selectedDigits H a B D) =
      D.filter fun v => GoodCenter R (selectedDigits H a B D) v := by
  classical
  ext v
  rw [mem_goodCenters, Finset.mem_filter]
  exact ⟨fun h => ⟨(Finset.mem_filter.mp h.1).1, h⟩, fun h => h.2⟩

theorem sum_goodCenters_card (R : ℕ) (H : ℤ) (F : Finset ℕ) (B D : Finset ℤ) :
    (∑ a ∈ F, (goodCenters R (selectedDigits H a B D)).card) =
      ∑ v ∈ D, (goodLabels R H v F B D).card := by
  classical
  simp only [goodCenters_selected_eq_filter, goodLabels,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

def liftedHost (H : ℤ) (F : Finset ℕ) (D : Finset ℤ) : Finset ℤ :=
  F.biUnion fun a => D.image (liftValue H a)

theorem selectedDigits_card_sum {H : ℤ} {F : Finset ℕ} {B D : Finset ℤ}
    (hpos : ∀ a ∈ F, 0 < a) (hsep : FiberSeparated H F D)
    (hB : B ⊆ liftedHost H F D) :
    B.card = ∑ a ∈ F, (selectedDigits H a B D).card := by
  classical
  let P := fun a => (selectedDigits H a B D).image (liftValue H a)
  have heq : B = F.biUnion P := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp (hB hx)
      obtain ⟨u, huD, rfl⟩ := Finset.mem_image.mp hxa
      apply Finset.mem_biUnion.mpr
      exact ⟨a, ha, Finset.mem_image.mpr
        ⟨u, Finset.mem_filter.mpr ⟨huD, hx⟩, rfl⟩⟩
    · intro hx
      obtain ⟨a, _, hxa⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxa
      exact (Finset.mem_filter.mp hu).2
  have hdisjoint : (F : Set ℕ).PairwiseDisjoint P := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxa
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hxb
    exact hab (hsep a ha u (Finset.mem_filter.mp hu).1 b hb v
      (Finset.mem_filter.mp hv).1 heq.symm).1
  calc
    B.card = (F.biUnion P).card := congrArg Finset.card heq
    _ = ∑ a ∈ F, (P a).card := Finset.card_biUnion hdisjoint
    _ = ∑ a ∈ F, (selectedDigits H a B D).card := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.card_image_of_injective _ (liftValue_injective (hpos a ha))

/-- A repeated-sum bound on the coarse host yields a distinct-sum bound after lifting. -/
theorem liftedHost_independentBound {R K M : ℕ} {H : ℤ} {F : Finset ℕ}
    {D : Finset ℤ} (hpos : ∀ a ∈ F, 0 < a) (hsep : FiberSeparated H F D)
    (hcenters : CenterRich R K D)
    (hcoarse : ∀ C ⊆ F, RepeatedSumFree R C → C.card ≤ M)
    {B : Finset ℤ} (hB : B ⊆ liftedHost H F D) (hfree : Erdos790.IsSumFree B) :
    B.card ≤ D.card * M + F.card * K := by
  classical
  calc
    B.card = ∑ a ∈ F, (selectedDigits H a B D).card :=
      selectedDigits_card_sum hpos hsep hB
    _ ≤ ∑ a ∈ F, ((goodCenters R (selectedDigits H a B D)).card + K) := by
      apply Finset.sum_le_sum
      intro a _
      exact hcenters.card_le (Finset.filter_subset _ _)
    _ = (∑ v ∈ D, (goodLabels R H v F B D).card) + F.card * K := by
      rw [Finset.sum_add_distrib, sum_goodCenters_card]
      simp
    _ ≤ D.card * M + F.card * K := by
      apply Nat.add_le_add_right
      calc
        (∑ v ∈ D, (goodLabels R H v F B D).card) ≤ ∑ _v ∈ D, M := by
          apply Finset.sum_le_sum
          intro v _
          exact hcoarse _ (Finset.filter_subset _ _)
            (goodLabels_repeatedSumFree hpos hsep hfree)
        _ = D.card * M := by simp

end Erdos790.Upper
