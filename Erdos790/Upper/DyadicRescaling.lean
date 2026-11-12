import Erdos790.Upper.DyadicMeans
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-!
# Integral dyadic weights relative to an earlier level
-/

namespace Erdos790.Upper

def shiftedLevelWeight (a : ℕ) (p : ℕ × ℤ) : ℕ := 2 ^ (p.1 - a)
def shiftedLevelMoment (a : ℕ) (p : ℕ × ℤ) : ℤ := (2 : ℤ) ^ (p.1 - a) * p.2

theorem shifted_weight_sum_mul (L : List (ℕ × ℤ)) (a : ℕ)
    (hlevel : ∀ p ∈ L, a ≤ p.1) :
    (L.map (shiftedLevelWeight a)).sum * 2 ^ a = (L.map levelWeight).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : a ≤ p.1 := hlevel p (by simp)
    have hL : ∀ q ∈ L, a ≤ q.1 := fun q hq => hlevel q (by simp [hq])
    simp only [List.map_cons, List.sum_cons, add_mul]
    rw [ih hL]
    congr 1
    dsimp [shiftedLevelWeight, levelWeight]
    rw [← pow_add, Nat.sub_add_cancel hp]

theorem shifted_moment_sum_mul (L : List (ℕ × ℤ)) (a : ℕ)
    (hlevel : ∀ p ∈ L, a ≤ p.1) :
    (L.map (shiftedLevelMoment a)).sum * (2 : ℤ) ^ a = (L.map levelMoment).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : a ≤ p.1 := hlevel p (by simp)
    have hL : ∀ q ∈ L, a ≤ q.1 := fun q hq => hlevel q (by simp [hq])
    simp only [List.map_cons, List.sum_cons, add_mul]
    rw [ih hL]
    congr 1
    dsimp [shiftedLevelMoment, levelMoment]
    calc
      (2 : ℤ) ^ (p.1 - a) * p.2 * 2 ^ a = (2 ^ (p.1 - a) * 2 ^ a) * p.2 := by ring
      _ = 2 ^ p.1 * p.2 := by rw [← pow_add, Nat.sub_add_cancel hp]

theorem shifted_dyadic_sums {L : List (ℕ × ℤ)} {a j : ℕ} {head : ℤ}
    (hlevel : ∀ p ∈ L, a ≤ p.1) (haj : a ≤ j)
    (hmass : (L.map levelWeight).sum = 2 ^ j)
    (hmoment : (L.map levelMoment).sum = (2 : ℤ) ^ j * head) :
    (L.map (shiftedLevelWeight a)).sum = 2 ^ (j - a) ∧
      (L.map (shiftedLevelMoment a)).sum = (2 : ℤ) ^ (j - a) * head := by
  constructor
  · apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos a)
    rw [shifted_weight_sum_mul L a hlevel, hmass, ← pow_add, Nat.sub_add_cancel haj]
  · apply mul_right_cancel₀ (pow_ne_zero a (by decide : (2 : ℤ) ≠ 0))
    rw [shifted_moment_sum_mul L a hlevel, hmoment]
    rw [show (2 : ℤ) ^ j = 2 ^ (j - a) * 2 ^ a by rw [← pow_add, Nat.sub_add_cancel haj]]
    ring

theorem DyadicMean.rescaled_witness {S : ℕ → Finset ℤ} {cut head : ℤ} {a j : ℕ}
    (h : DyadicMean S cut j head) (haj : a ≤ j)
    (hS : ∀ k, ∀ t ∈ S k, a ≤ k) :
    ∃ L : List (ℕ × ℤ),
      (∀ p ∈ L, p.1 < j ∧ p.2 ∈ S p.1) ∧
      (L.map (shiftedLevelWeight a)).sum = 2 ^ (j - a) ∧
      (L.map (shiftedLevelMoment a)).sum = (2 : ℤ) ^ (j - a) * head ∧
      (∃ p ∈ L, p.2 < cut) ∧ (∃ p ∈ L, cut ≤ p.2) ∧
      L.length ≤ 2 ^ (j - a) := by
  obtain ⟨L, hL, hmass, hmoment, hleft, hright⟩ := h
  have hlevel : ∀ p ∈ L, a ≤ p.1 := fun p hp => hS p.1 p.2 (hL p hp).2
  obtain ⟨hmass', hmoment'⟩ := shifted_dyadic_sums hlevel haj hmass hmoment
  exact ⟨L, hL, hmass', hmoment', hleft, hright, dyadic_list_length_le hlevel hmass haj⟩

theorem sum_list_map_eq_sum_fin_get {α R : Type*} [AddCommMonoid R]
    (L : List α) (f : α → R) :
    (L.map f).sum = ∑ i : Fin L.length, f (L.get i) := by
  have hlist : List.ofFn (fun i : Fin L.length => f (L.get i)) = L.map f := by
    rw [← Function.comp_def, ← List.map_ofFn, List.ofFn_get]
  rw [← hlist, Fin.sum_ofFn]

theorem DyadicMean.finite_rescaled_witness {S : ℕ → Finset ℤ} {cut head : ℤ}
    {base start j : ℕ} (h : DyadicMean S cut j head)
    (hbase : base ≤ start) (hstart : start ≤ j)
    (hS : ∀ k, ∀ t ∈ S k, start ≤ k) :
    ∃ n : ℕ, ∃ level : Fin n → ℕ, ∃ coordinate : Fin n → ℤ,
      (∀ i, start ≤ level i ∧ level i < j ∧ coordinate i ∈ S (level i)) ∧
      (∑ i : Fin n, (2 : ℤ) ^ (level i - base)) = (2 : ℤ) ^ (j - base) ∧
      (∑ i : Fin n, (2 : ℤ) ^ (level i - base) * coordinate i) = (2 : ℤ) ^ (j - base) * head ∧
      (∃ i : Fin n, coordinate i < cut) ∧ (∃ i : Fin n, cut ≤ coordinate i) ∧
      n ≤ 2 ^ (j - start) := by
  obtain ⟨L, hL, hmass, hmoment, hleft, hright⟩ := h
  have hlevels : ∀ p ∈ L, start ≤ p.1 := fun p hp => hS p.1 p.2 (hL p hp).2
  obtain ⟨hmass', hmoment'⟩ := shifted_dyadic_sums
    (fun p hp => hbase.trans (hlevels p hp)) (hbase.trans hstart) hmass hmoment
  refine ⟨L.length, (fun i => (L.get i).1), (fun i => (L.get i).2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi := List.get_mem L i
    exact ⟨hlevels _ hi, (hL _ hi).1, (hL _ hi).2⟩
  · have hmassFin : (∑ i : Fin L.length, (2 : ℕ) ^ ((L.get i).1 - base)) = 2 ^ (j - base) := by
      simpa only [sum_list_map_eq_sum_fin_get, shiftedLevelWeight] using hmass'
    exact_mod_cast hmassFin
  · simpa only [sum_list_map_eq_sum_fin_get, shiftedLevelMoment] using hmoment'
  · obtain ⟨p, hp, hpCut⟩ := hleft
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
    exact ⟨i, hpCut⟩
  · obtain ⟨p, hp, hpCut⟩ := hright
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
    exact ⟨i, hpCut⟩
  · exact dyadic_list_length_le hlevels hmass hstart

theorem dyadic_residual_identity {ι : Type*} (I : Finset ι)
    (level : ι → ℕ) (value : ι → ℤ) {earlier headLevel : ℕ} {headValue residual : ℤ}
    (hlevels : ∀ i ∈ I, earlier ≤ level i) (hhead : earlier ≤ headLevel)
    (hresidual : residual = (2 : ℤ) ^ (headLevel - earlier) * headValue -
      ∑ i ∈ I, (2 : ℤ) ^ (level i - earlier) * value i) :
    (2 : ℤ) ^ headLevel * headValue =
      (∑ i ∈ I, (2 : ℤ) ^ level i * value i) + (2 : ℤ) ^ earlier * residual := by
  have hsum : (2 : ℤ) ^ earlier * (∑ i ∈ I, (2 : ℤ) ^ (level i - earlier) * value i) =
      ∑ i ∈ I, (2 : ℤ) ^ level i * value i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (hlevels i hi)]
  have hpower : (2 : ℤ) ^ earlier * (2 : ℤ) ^ (headLevel - earlier) = 2 ^ headLevel := by
    rw [← pow_add, Nat.add_sub_of_le hhead]
  rw [hresidual, mul_sub, ← mul_assoc, hpower, hsum]
  ring

end Erdos790.Upper
