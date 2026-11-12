import Erdos790.Upper.HeavyLevels
import Mathlib.Data.Nat.Dist

/-!
# Filling a positive residual from an earlier heavy level
-/

namespace Erdos790.Upper

theorem heavy_residual_impossible {C B : Finset ℕ} {R X K threshold i head N r : ℕ}
    (hX : 0 < X) (hC : ∀ u ∈ C, X ≤ u ∧ u < 2 * X)
    (hcover : SumCover C K threshold) (hheavy : K ≤ (levelSlice i C B).card)
    (hB : RepeatedSumFree R B) (hhead : head ∈ B)
    (near : List ℕ) (hnear : ∀ x ∈ near, x ∈ B)
    (hthreshold : threshold ≤ N) (hNlower : 2 * X ≤ N) (hNupper : N ≤ r * X)
    (harity : near.length + r ≤ R) (heq : head = near.sum + 2 ^ i * N) : False := by
  obtain ⟨terms, hterms, hsum⟩ := hcover (levelSlice i C B) (Finset.filter_subset _ _)
    hheavy N hthreshold
  have htermsC : ∀ x ∈ terms, x ∈ C := fun x hx => (Finset.mem_filter.mp (hterms x hx)).1
  have hlength := list_length_le_of_lower_bound hX
    (fun x hx => (hC x (htermsC x hx)).1) hsum hNupper
  have htwo := list_length_two_of_large_sum hX
    (fun x hx => (hC x (htermsC x hx)).2) hsum hNlower
  have hlift : ∀ x ∈ terms.map (fun u => 2 ^ i * u), x ∈ B := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    exact (Finset.mem_filter.mp (hterms u hu)).2
  have hcombined : ∀ x ∈ near ++ terms.map (fun u => 2 ^ i * u), x ∈ B := by
    intro x hx
    rcases List.mem_append.mp hx with hn | ht
    · exact hnear x hn
    · exact hlift x ht
  apply hB.not_list_sum hhead (near ++ terms.map (fun u => 2 ^ i * u)) hcombined
    (by simp only [List.length_append, List.length_map]; omega)
    (by simp only [List.length_append, List.length_map]; omega)
  rw [List.sum_append, sum_dilate_list, hsum]
  exact heq.symm

theorem two_point_residual_impossible {C B : Finset ℕ} {R X K threshold i j u v r : ℕ}
    (hX : 0 < X) (hC : ∀ x ∈ C, X ≤ x ∧ x < 2 * X)
    (hcover : SumCover C K threshold) (hheavy : K ≤ (levelSlice i C B).card)
    (hB : RepeatedSumFree R B) (hu : 2 ^ j * u ∈ B) (hv : 2 ^ j * v ∈ B)
    (hij : i ≤ j) (hthreshold : threshold ≤ 2 ^ (j - i) * Nat.dist u v)
    (hlower : 2 * X ≤ 2 ^ (j - i) * Nat.dist u v)
    (hupper : 2 ^ (j - i) * Nat.dist u v ≤ r * X) (harity : 1 + r ≤ R) : False := by
  have hlow : 2 ^ j * min u v ∈ B := by
    rcases le_total u v with huv | hvu
    · simpa only [min_eq_left huv] using hu
    · simpa only [min_eq_right hvu] using hv
  have hhigh : 2 ^ j * max u v ∈ B := by
    rcases le_total u v with huv | hvu
    · simpa only [max_eq_right huv] using hv
    · simpa only [max_eq_left hvu] using hu
  have hsplit : min u v + Nat.dist u v = max u v := by
    rw [Nat.dist_eq_max_sub_min]
    have hle : min u v ≤ max u v := min_le_max
    omega
  have hpower : 2 ^ i * 2 ^ (j - i) = (2 : ℕ) ^ j := by
    rw [← pow_add, Nat.add_sub_of_le hij]
  apply heavy_residual_impossible hX hC hcover hheavy hB hhigh [2 ^ j * min u v]
    (by simpa only [List.mem_singleton] using fun x hx => hx ▸ hlow)
    hthreshold hlower hupper (by simpa using harity)
  simp only [List.sum_cons, List.sum_nil, add_zero]
  rw [← Nat.mul_assoc, hpower, ← Nat.mul_add, hsplit]

end Erdos790.Upper
