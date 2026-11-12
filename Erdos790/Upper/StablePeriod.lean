import Erdos790.Upper.GapCounting
import Erdos790.Upper.DyadicMeans

/-!
# Charging selections during a stable lattice period

The midpoint sets grow monotonically. Their interval-cover invariant controls
the number of gaps, so the one-step bound telescopes over the period.
-/

open Finset

namespace Erdos790.Upper

theorem IntervalCovered.mono_length {m n : ℕ} {T : Finset ℤ}
    (hT : IntervalCovered m T) (hn : n ≤ m) : IntervalCovered n T := by
  intro x hx
  obtain ⟨a, b, ha, hb, hlength, hsubset⟩ := hT x hx
  exact ⟨a, b, ha, hb, by omega, hsubset⟩

theorem midpoint_step_card_bound {m M : ℕ} {T S U : Finset ℤ}
    (hT : T.Nonempty) (hcovered : IntervalCovered m T) (hm : 2 ≤ m)
    (hdisjoint : Disjoint T S) (hnext : midpointClosure T S ⊆ U) (hsize : T.card ≤ M) :
    S.card + 2 * T.card ≤ 2 * U.card + (M / m + 1) := by
  have hbound := midpoint_growth_bound hT hcovered hm hdisjoint
  have hsubset : T ⊆ midpointClosure T S := Finset.subset_union_left
  rw [Finset.card_sdiff_of_subset hsubset] at hbound
  have hcard := Finset.card_le_card hsubset
  have hnextcard := Finset.card_le_card hnext
  have hends : (rightEnds T).card ≤ M / m :=
    (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr
      ((rightEnds_card_mul_le hcovered).trans hsize)
  omega

theorem stable_period_mass_bound (T S : ℕ → Finset ℤ) (k m M : ℕ)
    (hm : 2 ≤ m)
    (hnonempty : ∀ i < k, (T i).Nonempty)
    (hcovered : ∀ i < k, IntervalCovered m (T i))
    (hdisjoint : ∀ i < k, Disjoint (T i) (S i))
    (hnext : ∀ i < k, midpointClosure (T i) (S i) ⊆ T (i + 1))
    (hsize : ∀ i ≤ k, (T i).card ≤ M) :
    (∑ i ∈ Finset.range k, (S i).card) ≤ 2 * M + k * (M / m + 1) := by
  have hsteps : (∑ i ∈ Finset.range k, ((S i).card + 2 * (T i).card)) ≤
      ∑ i ∈ Finset.range k, (2 * (T (i + 1)).card + (M / m + 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hik := Finset.mem_range.mp hi
    exact midpoint_step_card_bound (hnonempty i hik) (hcovered i hik) hm
      (hdisjoint i hik) (hnext i hik) (hsize i hik.le)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, Nat.nsmul_eq_mul] at hsteps
  have hlast := Finset.sum_range_succ (fun i => (T i).card) k
  have hfirst := Finset.sum_range_succ' (fun i => (T i).card) k
  have hfinal := hsize k le_rfl
  have hbudget : k * (M / m + 1) = k * (M / m) + k := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

theorem stable_period_three_mul_bound (T S : ℕ → Finset ℤ) (k m M : ℕ)
    (hm : 2 ≤ m)
    (hnonempty : ∀ i < k, (T i).Nonempty)
    (hcovered : ∀ i < k, IntervalCovered m (T i))
    (hdisjoint : ∀ i < k, Disjoint (T i) (S i))
    (hnext : ∀ i < k, midpointClosure (T i) (S i) ⊆ T (i + 1))
    (hsize : ∀ i ≤ k, (T i).card ≤ M) (herror : k * (M / m + 1) ≤ M) :
    (∑ i ∈ Finset.range k, (S i).card) ≤ 3 * M := by
  have hbound := stable_period_mass_bound T S k m M hm hnonempty hcovered
    hdisjoint hnext hsize
  omega

def propagatedMeans (T : Finset ℤ) (S : ℕ → Finset ℤ) : ℕ → Finset ℤ
  | 0 => T
  | n + 1 => midpointClosure (propagatedMeans T S n) (S n)

theorem propagatedMeans_nonempty {T : Finset ℤ} (hT : T.Nonempty)
    (S : ℕ → Finset ℤ) (n : ℕ) : (propagatedMeans T S n).Nonempty := by
  induction n with
  | zero => exact hT
  | succ n ih => exact ih.mono Finset.subset_union_left

theorem propagatedMeans_covered {T : Finset ℤ} {m : ℕ}
    (hT : IntervalCovered m T) (S : ℕ → Finset ℤ) (n : ℕ) :
    IntervalCovered (m / 2 ^ n) (propagatedMeans T S n) := by
  induction n with
  | zero => simpa only [propagatedMeans, pow_zero, Nat.div_one] using hT
  | succ n ih =>
    simpa only [propagatedMeans, Nat.div_div_eq_div_mul, pow_succ] using
      ih.midpointClosure (S := S n)

theorem propagatedMeans_dyadic {T : Finset ℤ} {S : ℕ → Finset ℤ}
    {cut : ℤ} {start : ℕ} (hT : ∀ x ∈ T, DyadicMean S cut start x) (n : ℕ) :
    ∀ x ∈ propagatedMeans T (fun i => S (start + i)) n,
      DyadicMean S cut (start + n) x := by
  induction n with
  | zero => simpa only [propagatedMeans, Nat.add_zero] using hT
  | succ n ih =>
    simpa only [propagatedMeans, Nat.add_assoc] using dyadicMean_midpointClosure ih

theorem midpointClosure_subset_Icc {T S : Finset ℤ} {a b : ℤ}
    (hT : T ⊆ Finset.Icc a b) (hS : S ⊆ Finset.Icc a b) :
    midpointClosure T S ⊆ Finset.Icc a b := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxT | hxMid
  · exact hT hxT
  · obtain ⟨yz, hyz, rfl⟩ := Finset.mem_image.mp hxMid
    obtain ⟨hyz, _⟩ := Finset.mem_filter.mp hyz
    obtain ⟨hy, hz⟩ := Finset.mem_product.mp hyz
    obtain ⟨hay, hyb⟩ := Finset.mem_Icc.mp (hT hy)
    obtain ⟨haz, hzb⟩ := Finset.mem_Icc.mp (hS hz)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem propagatedMeans_subset_Icc {T : Finset ℤ} {S : ℕ → Finset ℤ} {a b : ℤ}
    (k : ℕ) (hT : T ⊆ Finset.Icc a b) (hS : ∀ i < k, S i ⊆ Finset.Icc a b) :
    ∀ i ≤ k, propagatedMeans T S i ⊆ Finset.Icc a b := by
  intro i
  induction i with
  | zero => exact fun _ => hT
  | succ i ih =>
    intro hi
    exact midpointClosure_subset_Icc (ih (by omega)) (hS i (by omega))

theorem propagated_period_three_mul_bound {T : Finset ℤ} {S : ℕ → Finset ℤ}
    {cut a b : ℤ} {start k m seedLength : ℕ}
    (hT : T.Nonempty) (hcovered : IntervalCovered seedLength T)
    (hm : 2 ≤ m) (hroom : m * 2 ^ k ≤ seedLength)
    (hmean : ∀ x ∈ T, DyadicMean S cut start x)
    (hforbidden : ∀ i < k, ∀ x ∈ S (start + i), ¬DyadicMean S cut (start + i) x)
    (hTinterval : T ⊆ Finset.Icc a b)
    (hSinterval : ∀ i < k, S (start + i) ⊆ Finset.Icc a b)
    (herror : k * ((Finset.Icc a b).card / m + 1) ≤ (Finset.Icc a b).card) :
    (∑ i ∈ Finset.range k, (S (start + i)).card) ≤ 3 * (Finset.Icc a b).card := by
  let Q := propagatedMeans T (fun i => S (start + i))
  apply stable_period_three_mul_bound Q (fun i => S (start + i)) k m _ hm
    (fun i _ => propagatedMeans_nonempty hT _ i) ?_ ?_ ?_ ?_ herror
  · intro i hi
    have hcover := propagatedMeans_covered hcovered (fun i => S (start + i)) i
    apply hcover.mono_length
    apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos i)).mpr
    exact (Nat.mul_le_mul_left m (Nat.pow_le_pow_right Nat.zero_lt_two hi.le)).trans hroom
  · intro i hi
    apply Finset.disjoint_left.mpr
    intro x hxQ hxS
    exact hforbidden i hi x hxS (propagatedMeans_dyadic hmean i x hxQ)
  · intro i _
    exact Finset.Subset.refl _
  · intro i hi
    exact Finset.card_le_card (propagatedMeans_subset_Icc k hTinterval hSinterval i hi)

end Erdos790.Upper
