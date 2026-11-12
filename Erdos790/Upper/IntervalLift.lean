import Erdos790.Upper.CenterCapacity
import Erdos790.Upper.FiberGeometry
import Erdos790.Upper.Packing
import Erdos790.Upper.CoarseBound

/-!
# A positive distinct-summand witness from the coarse construction
-/

open Finset

namespace Erdos790.Upper

theorem liftedHost_card {H : ℤ} {F : Finset ℕ} {D : Finset ℤ}
    (hpos : ∀ a ∈ F, 0 < a) (hsep : FiberSeparated H F D) :
    (liftedHost H F D).card = F.card * D.card := by
  classical
  have hdisjoint : (F : Set ℕ).PairwiseDisjoint
      (fun a => D.image (liftValue H a)) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hy
    exact hab (hsep a ha u hu b hb v hv heq.symm).1
  rw [liftedHost, Finset.card_biUnion hdisjoint]
  have himage : ∀ a ∈ F, (D.image (liftValue H a)).card = D.card :=
    fun a ha => Finset.card_image_of_injective _ (liftValue_injective (hpos a ha))
  simp only [Finset.sum_congr rfl himage, Finset.sum_const, smul_eq_mul]

theorem interval_lift_witness {R L m N : ℕ} {F : Finset ℕ}
    (hL : 0 < L) (hm : 0 < m) (hN : 0 < N)
    (hFcard : F.card = L * m) (hpos : ∀ a ∈ F, 0 < a)
    (hcenters : CenterRich R (N / L) (Finset.Icc 1 (N : ℤ)))
    (hcoarse : ∀ C ⊆ F, RepeatedSumFree R C → (C.card : ℝ) ≤ coarseConstant * m) :
    ∃ A : Finset ℤ, ∃ bound : ℕ,
      (∀ x ∈ A, 0 < x) ∧ A.card = N * L * m ∧ IndependentBound A bound ∧
      (bound : ℝ) * L ≤ (coarseConstant + 2) * A.card := by
  classical
  let D := Finset.Icc 1 (N : ℤ)
  let H : ℤ := (N * F.sup id + 1 : ℕ)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hD : ∀ u ∈ D, 0 ≤ u ∧ u ≤ N := by
    intro u hu
    have h := Finset.mem_Icc.mp hu
    omega
  have hshift : ∀ a ∈ F, (a : ℤ) * N < H := by
    intro a ha
    have hmax : a ≤ F.sup id := Finset.le_sup (f := id) ha
    have hnat : a * N < N * F.sup id + 1 := by nlinarith
    dsimp only [H]
    exact_mod_cast hnat
  have hsep : FiberSeparated H F D := fiberSeparated_of_bounds hH hpos hD hshift
  have hDcard : D.card = N := by
    dsimp [D]
    rw [Int.card_Icc]
    omega
  let coarseBound := Nat.ceil (coarseConstant * (m : ℝ))
  have hcoarseNat : ∀ C ⊆ F, RepeatedSumFree R C → C.card ≤ coarseBound := by
    intro C hCF hC
    have h := (hcoarse C hCF hC).trans (Nat.le_ceil (coarseConstant * (m : ℝ)))
    exact_mod_cast h
  let A := liftedHost H F D
  let bound := N * coarseBound + F.card * (N / L)
  have hAcard : A.card = N * L * m := by
    rw [liftedHost_card hpos hsep, hDcard, hFcard]
    ring
  have hApos : ∀ x ∈ A, 0 < x := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxa
    have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
    have ha0 : (0 : ℤ) < a := by exact_mod_cast hpos a ha
    dsimp [liftValue]
    exact mul_pos ha0 (by omega)
  have hAbound : IndependentBound A bound := by
    intro B hBA hB
    simpa only [hDcard] using
      liftedHost_independentBound hpos hsep hcenters hcoarseNat hBA hB
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hceil : (coarseBound : ℝ) ≤ (coarseConstant + 1) * m := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ coarseConstant * (m : ℝ) by
      exact mul_nonneg coarseConstant_pos.le (Nat.cast_nonneg m))).le
    change (coarseBound : ℝ) ≤ _ at h
    nlinarith
  have hdiv : (L : ℝ) * (N / L : ℕ) ≤ N := by
    exact_mod_cast Nat.mul_div_le N L
  have hterm : (F.card : ℝ) * (N / L : ℕ) ≤ (m : ℝ) * N := by
    rw [hFcard]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hbound : (bound : ℝ) ≤ (coarseConstant + 2) * N * m := by
    dsimp [bound]
    push_cast
    have hfirst := mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith
  refine ⟨A, bound, hApos, hAcard, hAbound, ?_⟩
  calc
    (bound : ℝ) * L ≤ ((coarseConstant + 2) * N * m) * L :=
      mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg L)
    _ = (coarseConstant + 2) * A.card := by rw [hAcard]; push_cast; ring

end Erdos790.Upper
