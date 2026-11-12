import Erdos790.Upper.Basic
import Erdos790.Upper.Layers

/-!
# Repeated relations and separated occupied levels

The list formulation records repeated summands directly. A sufficiently
large level with complete sum coverage forbids a later occupied level in
the specified range of dyadic distances.
-/

namespace Erdos790.Upper

theorem RepeatedSumFree.not_list_sum {B : Finset ℕ} {R a : ℕ}
    (hB : RepeatedSumFree R B) (ha : a ∈ B) (L : List ℕ)
    (hL : ∀ x ∈ L, x ∈ B) (hmin : 2 ≤ L.length) (hmax : L.length ≤ R) :
    L.sum ≠ a := by
  have hsubset : L.toFinset ⊆ B := by
    intro x hx
    exact hL x (List.mem_toFinset.mp hx)
  have hlength : ∑ x ∈ B, L.count x = L.length := by
    calc
      ∑ x ∈ B, L.count x = ∑ x ∈ L.toFinset, L.count x := by
        symm
        apply Finset.sum_subset hsubset
        intro x _ hx
        exact List.count_eq_zero_of_not_mem (fun h => hx (List.mem_toFinset.mpr h))
      _ = L.length := List.sum_toFinset_count_eq_length L
  have hsum : L.sum = ∑ x ∈ B, L.count x * x := by
    simpa using Finset.sum_list_count_of_subset L B hsubset
  intro heq
  apply hB a ha (fun x => L.count x) (by omega) (by omega)
  exact hsum.symm.trans heq

theorem sum_dilate_list (L : List ℕ) (c : ℕ) :
    (L.map (fun x => c * x)).sum = c * L.sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih, Nat.mul_add]

theorem list_length_le_of_lower_bound {L : List ℕ} {X N R : ℕ}
    (hX : 0 < X) (hL : ∀ x ∈ L, X ≤ x) (hsum : L.sum = N) (hN : N ≤ R * X) :
    L.length ≤ R := by
  have hlength : L.length * X ≤ L.sum := by
    calc
      L.length * X = (L.map (fun _ => X)).sum := by simp
      _ ≤ L.sum := by simpa using List.sum_le_sum (l := L) hL
  apply Nat.le_of_mul_le_mul_right (hc := hX)
  exact hlength.trans (hsum ▸ hN)

theorem list_length_two_of_large_sum {L : List ℕ} {X N : ℕ}
    (hX : 0 < X) (hL : ∀ x ∈ L, x < 2 * X)
    (hsum : L.sum = N) (hN : 2 * X ≤ N) : 2 ≤ L.length := by
  cases L with
  | nil => simp at hsum; omega
  | cons x L =>
    cases L with
    | nil => have hx := hL x (by simp); simp at hsum; omega
    | cons y L => simp

def SumCover (C : Finset ℕ) (K threshold : ℕ) : Prop :=
  ∀ S ⊆ C, K ≤ S.card → ∀ N : ℕ, threshold ≤ N →
    ∃ L : List ℕ, (∀ x ∈ L, x ∈ S) ∧ L.sum = N

theorem heavy_level_gap_impossible {C B : Finset ℕ} {X K P R i j : ℕ}
    (hX : 0 < X) (hC : ∀ u ∈ C, X ≤ u ∧ u < 2 * X)
    (hB : RepeatedSumFree R B) (hcover : SumCover C K (P * X))
    (hheavy : K ≤ (levelSlice i C B).card)
    (hoccupied : (levelSlice j C B).Nonempty) (hij : i < j)
    (hP : 2 ≤ P) (hgapLower : P ≤ 2 ^ (j - i))
    (hgapUpper : 2 ^ (j - i + 1) ≤ R) : False := by
  obtain ⟨u, hu⟩ := hoccupied
  obtain ⟨huC, huB⟩ := Finset.mem_filter.mp hu
  let N := 2 ^ (j - i) * u
  have hNlower : P * X ≤ N := by
    exact (Nat.mul_le_mul_right X hgapLower).trans
      (Nat.mul_le_mul_left _ (hC u huC).1)
  have hNupper : N ≤ R * X := by
    calc
      N ≤ 2 ^ (j - i) * (2 * X) := Nat.mul_le_mul_left _ (hC u huC).2.le
      _ = 2 ^ (j - i + 1) * X := by rw [pow_succ]; ac_rfl
      _ ≤ R * X := Nat.mul_le_mul_right X hgapUpper
  obtain ⟨L, hL, hsum⟩ := hcover (levelSlice i C B) (Finset.filter_subset _ _)
    hheavy N hNlower
  have hbase : ∀ x ∈ L, X ≤ x ∧ x < 2 * X := by
    intro x hx
    exact hC x (Finset.mem_filter.mp (hL x hx)).1
  have hmin : 2 ≤ L.length := list_length_two_of_large_sum hX
    (fun x hx => (hbase x hx).2) hsum
    ((Nat.mul_le_mul_right X hP).trans hNlower)
  have hmax : L.length ≤ R := list_length_le_of_lower_bound hX
    (fun x hx => (hbase x hx).1) hsum hNupper
  have hmem : ∀ x ∈ L.map (fun x => 2 ^ i * x), x ∈ B := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact (Finset.mem_filter.mp (hL a ha)).2
  apply hB.not_list_sum huB (L.map (fun x => 2 ^ i * x)) hmem
    (by simpa using hmin) (by simpa using hmax)
  · rw [sum_dilate_list, hsum]
    dsimp [N]
    rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le hij.le]

end Erdos790.Upper
