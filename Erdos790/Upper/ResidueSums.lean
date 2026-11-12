import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Nat
import Lean.Elab.Tactic.Omega

/-!
# From finite coefficient choices to unbounded positive sums
-/

namespace Erdos790.Upper

theorem coefficient_list {ι : Type*} (I : Finset ι) (value coefficient : ι → ℕ) :
    ∃ L : List ℕ,
      L.length = ∑ i ∈ I, coefficient i ∧
      L.sum = ∑ i ∈ I, coefficient i * value i ∧
      ∀ x ∈ L, ∃ i ∈ I, x = value i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨L, hlength, hsum, hmem⟩ := ih
    refine ⟨List.replicate (coefficient i) (value i) ++ L, ?_, ?_, ?_⟩
    · simp [hi, hlength]
    · simp [hi, hsum]
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hx
        exact ⟨i, Finset.mem_insert_self _ _, rfl⟩
      · obtain ⟨j, hj, hvalue⟩ := hmem x hx
        exact ⟨j, Finset.mem_insert_of_mem hj, hvalue⟩

theorem pad_residue_sum {S : Finset ℕ} {M X N : ℕ} (L : List ℕ)
    (hM : M ∈ S) (hMpos : 0 < M) (hX : 0 < X)
    (hS : ∀ x ∈ S, X ≤ x) (hL : ∀ x ∈ L, x ∈ S)
    (hmod : Nat.ModEq M L.sum N) (hsize : L.sum ≤ N) :
    ∃ T : List ℕ, (∀ x ∈ T, x ∈ S) ∧ T.sum = N ∧ T.length ≤ N / X := by
  obtain ⟨q, hq⟩ := hmod.dvd'
  have hqsum : L.sum + q * M = N := by
    rw [Nat.mul_comm q M, ← hq, Nat.add_sub_of_le hsize]
  let T := L ++ List.replicate q M
  have hT : ∀ x ∈ T, x ∈ S := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hL x hx
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hx
      exact hM
  have hsum : T.sum = N := by simpa [T] using hqsum
  refine ⟨T, hT, hsum, ?_⟩
  apply (Nat.le_div_iff_mul_le hX).mpr
  calc
    T.length * X = (T.map (fun _ => X)).sum := by simp
    _ ≤ T.sum := by
      simpa using List.sum_le_sum (l := T) (f := fun _ => X) (g := id)
        (fun x hx => hS x (hT x hx))
    _ = N := hsum

theorem residue_coverage_gives_sums {S : Finset ℕ} {M X bound : ℕ}
    (hM : M ∈ S) (hMpos : 0 < M) (hX : 0 < X)
    (hS : ∀ x ∈ S, X ≤ x)
    (hcover : ∀ N : ℕ, ∃ L : List ℕ,
      (∀ x ∈ L, x ∈ S) ∧ L.sum ≤ bound ∧ Nat.ModEq M L.sum N) :
    ∀ N : ℕ, bound ≤ N → ∃ T : List ℕ,
      (∀ x ∈ T, x ∈ S) ∧ T.sum = N ∧ T.length ≤ N / X := by
  intro N hN
  obtain ⟨L, hL, hsize, hmod⟩ := hcover N
  exact pad_residue_sum L hM hMpos hX hS hL hmod (hsize.trans hN)

end Erdos790.Upper
