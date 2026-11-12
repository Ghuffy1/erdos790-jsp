import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
import Lean.Elab.Tactic.Omega

/-!
# Filling an interval from short residue representatives

This is the exact-length padding step in the lattice seed. Residue coverage is
an explicit input to this lemma.
-/

open Finset

namespace Erdos790.Upper

theorem exact_length_sum_of_residue {D : Finset ℕ} {W K b N : ℕ}
    (hzero : 0 ∈ D) (hW : W ∈ D) (hWpos : 0 < W)
    (hD : ∀ x ∈ D, x ≤ W) (L : List ℕ)
    (hL : ∀ x ∈ L, x ∈ D) (hLK : L.length ≤ K)
    (hresidue : Nat.ModEq W L.sum N)
    (hlower : K * W ≤ N) (hupper : N ≤ (b - K) * W) :
    ∃ T : List ℕ, (∀ x ∈ T, x ∈ D) ∧ T.length = b ∧ T.sum = N := by
  have hsum : L.sum ≤ L.length * W := by
    calc
      L.sum ≤ (L.map fun _ => W).sum := by
        simpa using (List.sum_le_sum (l := L) (f := id) (g := fun _ => W)
          (fun x hx => hD x (hL x hx)))
      _ = L.length * W := by simp
  have hsumN : L.sum ≤ N := hsum.trans ((Nat.mul_le_mul_right W hLK).trans hlower)
  obtain ⟨q, hq⟩ := hresidue.dvd'
  have hqsum : L.sum + q * W = N := by
    rw [Nat.mul_comm q W, ← hq, Nat.add_sub_of_le hsumN]
  have hKb : K ≤ b := by
    apply Nat.le_of_mul_le_mul_right (c := W) (hc := hWpos)
    calc
      K * W ≤ N := hlower
      _ ≤ (b - K) * W := hupper
      _ ≤ b * W := Nat.mul_le_mul_right W (Nat.sub_le _ _)
  have hqN : q * W ≤ N := by omega
  have hlength : L.length + q ≤ b := by
    apply Nat.le_of_mul_le_mul_right (c := W) (hc := hWpos)
    calc
      (L.length + q) * W = L.length * W + q * W := Nat.add_mul _ _ _
      _ ≤ K * W + N := Nat.add_le_add (Nat.mul_le_mul_right W hLK) hqN
      _ ≤ K * W + (b - K) * W := Nat.add_le_add_left hupper _
      _ = b * W := by rw [← Nat.add_mul, Nat.add_sub_of_le hKb]
  refine ⟨L ++ List.replicate q W ++ List.replicate (b - (L.length + q)) 0, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with (hx | hx) | hx
    · exact hL x hx
    · exact hx.2 ▸ hW
    · exact hx.2 ▸ hzero
  · simp only [List.length_append, List.length_replicate]
    omega
  · simpa [List.sum_append, List.sum_replicate, Nat.mul_comm] using hqsum

end Erdos790.Upper
