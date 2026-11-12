import Erdos790.Upper.KneserGrowth
import Erdos790.Upper.ExactSums
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas

/-!
# Short residue representations and exact integer sums

The finite-group covering theorem supplies short representatives. Zeros and
copies of the largest digit then give the exact-length interval used for the
mixed-mean seed.
-/

open Finset
open scoped Pointwise

namespace Erdos790.Upper

theorem mem_nsmul_image_iff_list {A G : Type*} [DecidableEq A]
    [AddCommMonoid G] [DecidableEq G] (D : Finset A) (f : A → G)
    (n : ℕ) (x : G) :
    x ∈ n • D.image f ↔ ∃ L : List A,
      L.length = n ∧ (∀ a ∈ L, a ∈ D) ∧ (L.map f).sum = x := by
  induction n generalizing x with
  | zero =>
    constructor
    · intro hx
      have hx0 : x = 0 := by simpa using hx
      exact ⟨[], by simp, by simp, by simp [hx0]⟩
    · rintro ⟨L, hlength, _, hsum⟩
      have hnil : L = [] := List.length_eq_zero_iff.mp hlength
      subst L
      simpa using hsum.symm
  | succ n ih =>
    rw [succ_nsmul, Finset.mem_add]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨L, hlength, hL, hsum⟩ := (ih a).mp ha
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
      refine ⟨d :: L, by simp [hlength], ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hd
        · exact hL y hy
      · simp [hsum, add_comm]
    · rintro ⟨L, hlength, hL, hsum⟩
      cases L with
      | nil => simp at hlength
      | cons d L =>
        have hlength' : L.length = n := by simpa using hlength
        have hL' : ∀ a ∈ L, a ∈ D := fun a ha => hL a (List.mem_cons_of_mem _ ha)
        have htail : (L.map f).sum ∈ n • D.image f :=
          (ih _).mpr ⟨L, hlength', hL', rfl⟩
        refine ⟨(L.map f).sum, htail, f d, Finset.mem_image.mpr
          ⟨d, hL d (by simp), rfl⟩, ?_⟩
        simpa [add_comm] using hsum

theorem cyclic_residue_representatives_of_mem_closure {D : Finset ℕ} {W K : ℕ}
    (hW : 0 < W) (hzero : 0 ∈ D)
    (hlarge : 2 * W ≤ K * (D.image fun d : ℕ => (d : ZMod W)).card)
    (N : ℕ) (hNclosure : (N : ZMod W) ∈ AddSubgroup.closure
      ((D.image fun d : ℕ => (d : ZMod W)) : Set (ZMod W))) : ∃ L : List ℕ,
      L.length = K ∧ (∀ d ∈ L, d ∈ D) ∧ Nat.ModEq W L.sum N := by
  let : NeZero W := ⟨Nat.ne_of_gt hW⟩
  let P := D.image fun d : ℕ => (d : ZMod W)
  have hzeroP : (0 : ZMod W) ∈ P :=
    Finset.mem_image.mpr ⟨0, hzero, by simp⟩
  have hN : (N : ZMod W) ∈ K • P := mem_nsmul_of_mem_closure P hzeroP K
    (by simpa only [ZMod.card] using hlarge) hNclosure
  obtain ⟨L, hlength, hL, hsum⟩ :=
    (mem_nsmul_image_iff_list D (fun d : ℕ => (d : ZMod W)) K (N : ZMod W)).mp hN
  refine ⟨L, hlength, hL, (ZMod.natCast_eq_natCast_iff L.sum N W).mp ?_⟩
  rwa [← Nat.cast_list_sum] at hsum

theorem cyclic_residue_representatives {D : Finset ℕ} {W K : ℕ}
    (hW : 0 < W) (hzero : 0 ∈ D)
    (hgenerate : AddSubgroup.closure
      ((D.image fun d : ℕ => (d : ZMod W)) : Set (ZMod W)) = ⊤)
    (hlarge : 2 * W ≤ K * (D.image fun d : ℕ => (d : ZMod W)).card)
    (N : ℕ) : ∃ L : List ℕ,
      L.length = K ∧ (∀ d ∈ L, d ∈ D) ∧ Nat.ModEq W L.sum N := by
  apply cyclic_residue_representatives_of_mem_closure hW hzero hlarge N
  rw [hgenerate]
  trivial

theorem residue_mem_closure_of_gcd_dvd (D : Finset ℕ) (W N : ℕ)
    (hdiv : (D.image (fun d : ℕ => (d : ℤ))).gcd id ∣ (N : ℤ)) :
    (N : ZMod W) ∈ AddSubgroup.closure
      ((D.image fun d : ℕ => (d : ZMod W)) : Set (ZMod W)) := by
  let H := AddSubgroup.closure
    ((D.image fun d : ℕ => (d : ZMod W)) : Set (ZMod W))
  let f := Int.castAddHom (ZMod W)
  have hcontain : ((D.image fun d : ℕ => (d : ℤ)) : Set ℤ) ⊆ H.comap f := by
    intro z hz
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
    change ((d : ℤ) : ZMod W) ∈ H
    apply AddSubgroup.subset_closure
    exact Finset.mem_image.mpr ⟨d, hd, by simp⟩
  have hclosure := (AddSubgroup.closure_le (H.comap f)).mpr hcontain
  have hN : (N : ℤ) ∈ AddSubgroup.closure
      ((D.image fun d : ℕ => (d : ℤ)) : Set ℤ) := by
    rw [Int.closure_eq_zmultiples_finsetGcd, Int.mem_zmultiples_iff]
    exact hdiv
  have hresult := hclosure hN
  change f (N : ℤ) ∈ H at hresult
  simpa [f, H] using hresult

theorem residue_image_card_lower {D : Finset ℕ} {W : ℕ}
    (hD : ∀ d ∈ D, d ≤ W) :
    D.card - 1 ≤ (D.image fun d : ℕ => (d : ZMod W)).card := by
  let E := D.erase W
  have hinj : Set.InjOn (fun d : ℕ => (d : ZMod W)) (E : Set ℕ) := by
    intro d hd e he hde
    have hdlt : d < W := by
      have hb := hD d (Finset.mem_of_mem_erase hd)
      have hne := (Finset.mem_erase.mp hd).1
      omega
    have helt : e < W := by
      have hb := hD e (Finset.mem_of_mem_erase he)
      have hne := (Finset.mem_erase.mp he).1
      omega
    have hmod := (ZMod.natCast_eq_natCast_iff' d e W).mp hde
    simpa only [Nat.mod_eq_of_lt hdlt, Nat.mod_eq_of_lt helt] using hmod
  have hcard : (E.image fun d : ℕ => (d : ZMod W)).card = E.card :=
    Finset.card_image_iff.mpr hinj
  have herase : D.card - 1 ≤ E.card := by
    by_cases hW : W ∈ D
    · exact (Finset.card_erase_of_mem hW).symm.le
    · have heq : E = D := Finset.erase_eq_of_notMem hW
      rw [heq]
      exact Nat.sub_le _ _
  calc
    D.card - 1 ≤ E.card := herase
    _ = (E.image fun d : ℕ => (d : ZMod W)).card := hcard.symm
    _ ≤ (D.image fun d : ℕ => (d : ZMod W)).card :=
      Finset.card_le_card (Finset.image_subset_image (Finset.erase_subset _ _))

theorem exact_length_sum_of_cyclic_generation {D : Finset ℕ} {W K b N : ℕ}
    (hWpos : 0 < W) (hzero : 0 ∈ D) (hW : W ∈ D)
    (hD : ∀ x ∈ D, x ≤ W)
    (hgenerate : AddSubgroup.closure
      ((D.image fun d : ℕ => (d : ZMod W)) : Set (ZMod W)) = ⊤)
    (hlarge : 2 * W ≤ K * (D.image fun d : ℕ => (d : ZMod W)).card)
    (hlower : K * W ≤ N) (hupper : N ≤ (b - K) * W) :
    ∃ T : List ℕ, (∀ x ∈ T, x ∈ D) ∧ T.length = b ∧ T.sum = N := by
  obtain ⟨L, hlength, hL, hresidue⟩ :=
    cyclic_residue_representatives hWpos hzero hgenerate hlarge N
  exact exact_length_sum_of_residue hzero hW hWpos hD L hL hlength.le
    hresidue hlower hupper

theorem exact_length_sum_of_gcd_dvd {D : Finset ℕ} {W K b N : ℕ}
    (hWpos : 0 < W) (hzero : 0 ∈ D) (hW : W ∈ D)
    (hD : ∀ x ∈ D, x ≤ W) (hlarge : 2 * W ≤ K * (D.card - 1))
    (hdiv : (D.image (fun d : ℕ => (d : ℤ))).gcd id ∣ (N : ℤ))
    (hlower : K * W ≤ N) (hupper : N ≤ (b - K) * W) :
    ∃ T : List ℕ, (∀ x ∈ T, x ∈ D) ∧ T.length = b ∧ T.sum = N := by
  have hlarge' : 2 * W ≤ K * (D.image fun d : ℕ => (d : ZMod W)).card :=
    hlarge.trans (Nat.mul_le_mul_left K (residue_image_card_lower hD))
  obtain ⟨L, hlength, hL, hresidue⟩ :=
    cyclic_residue_representatives_of_mem_closure hWpos hzero hlarge' N
      (residue_mem_closure_of_gcd_dvd D W N hdiv)
  exact exact_length_sum_of_residue hzero hW hWpos hD L hL hlength.le
    hresidue hlower hupper

end Erdos790.Upper
