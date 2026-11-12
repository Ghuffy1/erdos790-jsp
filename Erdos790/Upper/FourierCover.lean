import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A Fourier criterion for complete residue coverage

The nontrivial character contributions are bounded in total by the trivial
contribution. Fourier inversion then forces every residue to occur.
-/

open Finset

namespace Erdos790.Upper

theorem dft_nonzero_of_tail {M : ℕ} [NeZero M] (f : ZMod M → ℂ)
    (htail : (∑ a ∈ (Finset.univ : Finset (ZMod M)).erase 0,
      ‖ZMod.dft f a‖) < ‖ZMod.dft f 0‖) (x : ZMod M) : f x ≠ 0 := by
  intro hx
  let term := fun a : ZMod M =>
    ZMod.stdAddChar (-(a * (-x))) * ZMod.dft f a
  have hsum : ∑ a, term a = 0 := by
    have h := congr_fun (ZMod.dft_dft f) (-x)
    simpa only [ZMod.dft_apply, term, smul_eq_mul, neg_neg, hx, mul_zero] using h
  have hzero : term 0 = ZMod.dft f 0 := by simp [term]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (ZMod M)) term
    (Finset.mem_univ (0 : ZMod M))
  have hvalue : ZMod.dft f 0 = -(∑ a ∈ (Finset.univ : Finset (ZMod M)).erase 0,
      term a) := by rw [hsum, hzero] at hsplit; linear_combination hsplit
  have hnorm : ‖ZMod.dft f 0‖ ≤
      ∑ a ∈ (Finset.univ : Finset (ZMod M)).erase 0, ‖ZMod.dft f a‖ := by
    rw [hvalue, norm_neg]
    calc
      ‖∑ a ∈ (Finset.univ : Finset (ZMod M)).erase 0, term a‖ ≤
          ∑ a ∈ (Finset.univ : Finset (ZMod M)).erase 0, ‖term a‖ := norm_sum_le _ _
      _ = ∑ a ∈ (Finset.univ : Finset (ZMod M)).erase 0, ‖ZMod.dft f a‖ := by
        apply Finset.sum_congr rfl
        intro a _
        simp [term]
  exact (not_le_of_gt htail) hnorm

theorem finite_residue_coverage {Ω : Type*} [Fintype Ω] {M : ℕ} [NeZero M]
    (value : Ω → ZMod M)
    (htail : (∑ a ∈ (Finset.univ : Finset (ZMod M)).erase 0,
      ‖∑ z : Ω, ZMod.stdAddChar (-(value z * a))‖) < Fintype.card Ω)
    (x : ZMod M) : ∃ z : Ω, value z = x := by
  classical
  let f : ZMod M → ℂ := fun y => ∑ z : Ω, if value z = y then 1 else 0
  have htransform : ∀ a : ZMod M,
      ZMod.dft f a = ∑ z : Ω, ZMod.stdAddChar (-(value z * a)) := by
    intro a
    simp only [ZMod.dft_apply, f, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    simp [eq_comm]
  have htrivial : ‖ZMod.dft f 0‖ = Fintype.card Ω := by
    rw [htransform]
    simp
  have hnonzero : f x ≠ 0 := dft_nonzero_of_tail f (by simpa [htransform, htrivial] using htail) x
  by_contra hnone
  have hno : ∀ z : Ω, value z ≠ x := by simpa using hnone
  apply hnonzero
  simp [f, hno]

theorem addChar_finset_sum {ι G R : Type*} [AddCommMonoid G] [CommMonoid R]
    (χ : AddChar G R) (s : Finset ι) (f : ι → G) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]

theorem independent_character_sum {ι α G R : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [AddCommMonoid G] [CommSemiring R] (χ : AddChar G R) (f : ι → α → G) :
    (∑ z : ι → α, χ (∑ i, f i (z i))) = ∏ i, ∑ a, χ (f i a) := by
  classical
  simp only [addChar_finset_sum]
  exact (Fintype.prod_sum (fun i a => χ (f i a))).symm

end Erdos790.Upper
