import Erdos790.External.Kneser
import Mathlib.Tactic.Ring

/-!
# Iterating Kneser's inequality

The imported theorem is the formalization by Mantas Bakšys and Yaël Dillies.
This file records the cardinality inequality for repeated sumsets used in the
residue-coverage argument.
-/

open Finset
open scoped Pointwise

namespace Erdos790.Upper

theorem kneser_nsmul_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    (P : Finset G) (hP : P.Nonempty) (n : ℕ) (hn : 0 < n) :
    n * P.card ≤ (n • P).card + (n - 1) * (n • P).addStab.card := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hnzero : n = 0
    · subst n
      simp
    have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
    have hprev := ih hnpos
    let H := (n • P + P).addStab
    have hsum_nonempty : (n • P + P).Nonempty := hP.nsmul.add hP
    have hH_nonempty : H.Nonempty := hsum_nonempty.addStab
    have hstep := Finset.add_kneser (n • P) P
    have hcardN : (n • P).card ≤ (n • P + H).card :=
      Finset.card_le_card_add_right hH_nonempty
    have hcardP : P.card ≤ (P + H).card := Finset.card_le_card_add_right hH_nonempty
    have hgrowth : (n • P).card + P.card ≤ (n • P + P).card + H.card :=
      (Nat.add_le_add hcardN hcardP).trans hstep
    have hstab : (n • P).addStab.card ≤ H.card :=
      Finset.card_le_card (Finset.subset_addStab_add_left hP)
    have hprev' : n * P.card ≤ (n • P).card + (n - 1) * H.card :=
      hprev.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (n - 1) hstab) _)
    have hcombine : (n - 1) * H.card + H.card = n * H.card := by
      calc
        (n - 1) * H.card + H.card = (n - 1 + 1) * H.card := by
          simp only [Nat.add_mul, Nat.one_mul]
        _ = n * H.card := by congr 1; omega
    calc
      (n + 1) * P.card = n * P.card + P.card := by
        simp only [Nat.add_mul, Nat.one_mul]
      _ ≤ ((n • P).card + (n - 1) * H.card) + P.card :=
        Nat.add_le_add_right hprev' _
      _ = ((n • P).card + P.card) + (n - 1) * H.card := by omega
      _ ≤ ((n • P + P).card + H.card) + (n - 1) * H.card :=
        Nat.add_le_add_right hgrowth _
      _ = (n • P + P).card + n * H.card := by omega
      _ = ((n + 1) • P).card + (n + 1 - 1) * ((n + 1) • P).addStab.card := by
        simp only [succ_nsmul, Nat.add_sub_cancel_right, H]

theorem nsmul_addStab_eq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (n : ℕ) (hn : 0 < n) : n • S.addStab = S.addStab := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul, ih (by omega), Finset.addStab_add_addStab]

/-- If the final stabilizer has at least two cosets meeting `P`, repeated sums
grow at least linearly at half the cardinality of `P`. -/
theorem kneser_nsmul_card_two_cosets_lt {G : Type*} [AddCommGroup G] [DecidableEq G]
    (P : Finset G) (hP : P.Nonempty) (n : ℕ) (hn : 0 < n)
    (hcosets : 2 * (n • P).addStab.card ≤ (P + (n • P).addStab).card) :
    n * P.card < 2 * (n • P).card := by
  let S := n • P
  let H := S.addStab
  let Q := P + H
  have hQ : Q.Nonempty := hP.add (hP.nsmul.addStab)
  have hQsum : n • Q = S := by
    dsimp [Q, H, S]
    rw [nsmul_add, nsmul_addStab_eq _ _ hn, Finset.add_addStab]
  have hbound := kneser_nsmul_card Q hQ n hn
  rw [hQsum] at hbound
  have hcosets' : 2 * H.card ≤ Q.card := hcosets
  have hprev : (n - 1) * (2 * H.card) ≤ (n - 1) * Q.card :=
    Nat.mul_le_mul_left (n - 1) hcosets'
  have hdouble : 2 * (n * Q.card) ≤ 2 * S.card + (n - 1) * Q.card := by
    calc
      2 * (n * Q.card) ≤ 2 * (S.card + (n - 1) * H.card) :=
        Nat.mul_le_mul_left 2 hbound
      _ = 2 * S.card + (n - 1) * (2 * H.card) := by ring
      _ ≤ 2 * S.card + (n - 1) * Q.card := Nat.add_le_add_left hprev _
  have hsplit : (n - 1) * Q.card + Q.card = n * Q.card := by
    calc
      (n - 1) * Q.card + Q.card = (n - 1 + 1) * Q.card := by
        simp only [Nat.add_mul, Nat.one_mul]
      _ = n * Q.card := by congr 1; omega
  have hfinal : n * Q.card < 2 * S.card := by
    have hQpos := hQ.card_pos
    omega
  have hcard : P.card ≤ Q.card := Finset.card_le_card_add_right (hP.nsmul.addStab)
  exact (Nat.mul_le_mul_left n hcard).trans_lt hfinal

theorem kneser_nsmul_card_two_cosets {G : Type*} [AddCommGroup G] [DecidableEq G]
    (P : Finset G) (hP : P.Nonempty) (n : ℕ) (hn : 0 < n)
    (hcosets : 2 * (n • P).addStab.card ≤ (P + (n • P).addStab).card) :
    n * P.card ≤ 2 * (n • P).card :=
  (kneser_nsmul_card_two_cosets_lt P hP n hn hcosets).le

theorem addStab_two_cosets {G : Type*} [AddCommGroup G] [DecidableEq G]
    {S P : Finset G} (hS : S.Nonempty) (hzero : 0 ∈ P)
    {p : G} (hp : p ∈ P) (hpH : p ∉ S.addStab) :
    2 * S.addStab.card ≤ (P + S.addStab).card := by
  let H := S.addStab
  have hzH : 0 ∈ H := Finset.zero_mem_addStab.mpr hS
  have hnot : ¬p +ᵥ H ⊆ (0 : Finset G) + H := by
    intro hsub
    have hmem := hsub (Finset.vadd_mem_vadd_finset hzH)
    exact hpH (by simpa using hmem)
  have hdis : Disjoint (p +ᵥ H) H := by
    simpa only [zero_add] using
      (Finset.disjoint_vadd_finset_addStab_add_addStab (s := S) (t := 0) hnot)
  have hsubH : H ⊆ P + H := by
    intro x hx
    simpa only [zero_add] using Finset.add_mem_add hzero hx
  have hsubpH : p +ᵥ H ⊆ P + H := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_vadd_finset.mp hx
    exact Finset.add_mem_add hp hy
  calc
    2 * H.card = (H ∪ (p +ᵥ H)).card := by
      rw [Finset.card_union_of_disjoint hdis.symm, Finset.card_vadd_finset]
      omega
    _ ≤ (P + H).card := Finset.card_le_card (Finset.union_subset hsubH hsubpH)

/-- This many sums cover every element of the subgroup generated by `P`. -/
theorem mem_nsmul_of_mem_closure {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (P : Finset G) (hzero : 0 ∈ P) (n : ℕ)
    (hlarge : 2 * Fintype.card G ≤ n * P.card)
    {x : G} (hx : x ∈ AddSubgroup.closure (P : Set G)) : x ∈ n • P := by
  classical
  have hP : P.Nonempty := ⟨0, hzero⟩
  have hn : 0 < n := by
    have hG := Fintype.card_pos (α := G)
    by_contra h
    have hn0 : n = 0 := by omega
    simp only [hn0, zero_mul] at hlarge
    omega
  let S := n • P
  have hS : S.Nonempty := hP.nsmul
  have hzall : ∀ k : ℕ, (0 : G) ∈ k • P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul]
      simpa using Finset.add_mem_add ih hzero
  have hzS : (0 : G) ∈ S := hzall n
  by_contra hproper
  have hout : ∃ p ∈ P, p ∉ S.addStab := by
    by_contra h
    push Not at h
    have hclosure : AddSubgroup.closure (P : Set G) ≤
        AddAction.stabilizer G (S : Set G) := by
      apply (AddSubgroup.closure_le _).mpr
      intro p hp
      have hpH : p ∈ (S.addStab : Set G) := h p hp
      rwa [Finset.coe_addStab hS] at hpH
    have hg := hclosure hx
    have hgH : x ∈ S.addStab := by
      have heq := Finset.coe_addStab hS
      change x ∈ (AddAction.stabilizer G (S : Set G) : Set G) at hg
      rw [← heq] at hg
      exact hg
    have hsame := (Finset.mem_addStab hS).mp hgH
    have hmem := Finset.vadd_mem_vadd_finset (a := x) hzS
    rw [hsame] at hmem
    apply hproper
    simpa using hmem
  obtain ⟨p, hp, hpH⟩ := hout
  have hcosets := addStab_two_cosets hS hzero hp hpH
  have hsmall := kneser_nsmul_card_two_cosets_lt P hP n hn hcosets
  have hcard : S.card ≤ Fintype.card G := Finset.card_le_univ _
  change n * P.card < 2 * S.card at hsmall
  omega

/-- A generating set containing zero covers the finite group after this many sums. -/
theorem nsmul_eq_univ_of_card {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (P : Finset G) (hzero : 0 ∈ P)
    (hgenerate : AddSubgroup.closure (P : Set G) = ⊤) (n : ℕ)
    (hlarge : 2 * Fintype.card G ≤ n * P.card) : n • P = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  apply mem_nsmul_of_mem_closure P hzero n hlarge
  rw [hgenerate]
  trivial

end Erdos790.Upper
