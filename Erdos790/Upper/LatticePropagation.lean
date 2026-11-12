import Erdos790.Upper.StablePeriod

/-!
# Propagation in integer coordinates of a lattice

The mixed-mean witnesses remain in the original selected-point system. Only
the midpoint counting uses coordinates in the current lattice.
-/

namespace Erdos790.Upper

theorem affine_dyadicMean_midpointClosure {S : ℕ → Finset ℤ} {T C : Finset ℤ}
    {cut u g : ℤ} {j : ℕ}
    (hT : ∀ x ∈ T, DyadicMean S cut j (u + g * x))
    (hC : ∀ y ∈ C, u + g * y ∈ S j) :
    ∀ x ∈ midpointClosure T C, DyadicMean S cut (j + 1) (u + g * x) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (hT x hx).carry
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hp, heven⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpT, hpC⟩ := Finset.mem_product.mp hp
    apply (hT p.1 hpT).midpoint (hC p.2 hpC)
    have heq : 2 * ((p.1 + p.2) / 2) = p.1 + p.2 := by omega
    calc
      2 * (u + g * ((p.1 + p.2) / 2)) =
          2 * u + g * (2 * ((p.1 + p.2) / 2)) := by ring
      _ = (u + g * p.1) + (u + g * p.2) := by rw [heq]; ring

theorem propagatedMeans_affine_dyadic {S : ℕ → Finset ℤ}
    {T : Finset ℤ} {C : ℕ → Finset ℤ} {cut u g : ℤ} {start k : ℕ}
    (hT : ∀ x ∈ T, DyadicMean S cut start (u + g * x))
    (hC : ∀ i < k, ∀ y ∈ C i, u + g * y ∈ S (start + i)) :
    ∀ n ≤ k, ∀ x ∈ propagatedMeans T C n,
      DyadicMean S cut (start + n) (u + g * x) := by
  intro n
  induction n with
  | zero => simpa only [propagatedMeans, Nat.add_zero] using fun _ => hT
  | succ n ih =>
    intro hn
    have hprevious := ih (by omega)
    have hnext := affine_dyadicMean_midpointClosure hprevious (hC n (by omega))
    simpa only [propagatedMeans, Nat.add_assoc] using hnext

theorem propagated_lattice_period_three_mul_bound
    {S : ℕ → Finset ℤ} {T : Finset ℤ} {C : ℕ → Finset ℤ}
    {cut u g a b : ℤ} {start k m seedLength : ℕ}
    (hT : T.Nonempty) (hcovered : IntervalCovered seedLength T)
    (hm : 2 ≤ m) (hroom : m * 2 ^ k ≤ seedLength)
    (hmean : ∀ x ∈ T, DyadicMean S cut start (u + g * x))
    (hC : ∀ i < k, ∀ y ∈ C i, u + g * y ∈ S (start + i))
    (hforbidden : ∀ i < k, ∀ x ∈ C i,
      ¬DyadicMean S cut (start + i) (u + g * x))
    (hTinterval : T ⊆ Finset.Icc a b)
    (hCinterval : ∀ i < k, C i ⊆ Finset.Icc a b)
    (herror : k * ((Finset.Icc a b).card / m + 1) ≤ (Finset.Icc a b).card) :
    (∑ i ∈ Finset.range k, (C i).card) ≤ 3 * (Finset.Icc a b).card := by
  let Q := propagatedMeans T C
  apply stable_period_three_mul_bound Q C k m _ hm
    (fun i _ => propagatedMeans_nonempty hT _ i) ?_ ?_ ?_ ?_ herror
  · intro i hi
    have hcover := propagatedMeans_covered hcovered C i
    apply hcover.mono_length
    apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos i)).mpr
    exact (Nat.mul_le_mul_left m (Nat.pow_le_pow_right Nat.zero_lt_two hi.le)).trans hroom
  · intro i hi
    apply Finset.disjoint_left.mpr
    intro x hxQ hxC
    exact hforbidden i hi x hxC
      (propagatedMeans_affine_dyadic hmean hC i hi.le x hxQ)
  · intro i _
    exact Finset.Subset.refl _
  · intro i hi
    exact Finset.card_le_card (propagatedMeans_subset_Icc k hTinterval hCinterval i hi)

end Erdos790.Upper
