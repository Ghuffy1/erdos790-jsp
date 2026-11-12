import Erdos790.Upper.MidpointCounting
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Exact mixed dyadic means

The list permits repeated selected points. Its integer weights record the
levels of those points. Both sides of the cut must occur in the list.
-/

open Finset

namespace Erdos790.Upper

def levelWeight (p : ℕ × ℤ) : ℕ := 2 ^ p.1

def levelMoment (p : ℕ × ℤ) : ℤ := 2 ^ p.1 * p.2

def DyadicMean (S : ℕ → Finset ℤ) (cut : ℤ) (j : ℕ) (t : ℤ) : Prop :=
  ∃ L : List (ℕ × ℤ),
    (∀ p ∈ L, p.1 < j ∧ p.2 ∈ S p.1) ∧
    (L.map levelWeight).sum = 2 ^ j ∧
    (L.map levelMoment).sum = (2 : ℤ) ^ j * t ∧
    (∃ p ∈ L, p.2 < cut) ∧ (∃ p ∈ L, cut ≤ p.2)

theorem DyadicMean.carry {S : ℕ → Finset ℤ} {cut t : ℤ} {j : ℕ}
    (h : DyadicMean S cut j t) : DyadicMean S cut (j + 1) t := by
  obtain ⟨L, hL, hweight, hmoment, hleft, hright⟩ := h
  refine ⟨L ++ L, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨by have := (hL p hp).1; omega, (hL p hp).2⟩
    · exact ⟨by have := (hL p hp).1; omega, (hL p hp).2⟩
  · simp only [List.map_append, List.sum_append, hweight, pow_succ]
    omega
  · rw [List.map_append, List.sum_append, hmoment, pow_succ]
    ring
  · obtain ⟨p, hp, hcut⟩ := hleft
    exact ⟨p, List.mem_append.mpr (Or.inl hp), hcut⟩
  · obtain ⟨p, hp, hcut⟩ := hright
    exact ⟨p, List.mem_append.mpr (Or.inl hp), hcut⟩

theorem DyadicMean.midpoint {S : ℕ → Finset ℤ} {cut x y t : ℤ} {j : ℕ}
    (h : DyadicMean S cut j x) (hy : y ∈ S j) (ht : 2 * t = x + y) :
    DyadicMean S cut (j + 1) t := by
  obtain ⟨L, hL, hweight, hmoment, hleft, hright⟩ := h
  refine ⟨(j, y) :: L, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨by omega, hy⟩
    · exact ⟨by have := (hL p hp).1; omega, (hL p hp).2⟩
  · simp only [List.map_cons, List.sum_cons, levelWeight, hweight, pow_succ]
    omega
  · simp only [List.map_cons, List.sum_cons, levelMoment, hmoment, pow_succ]
    calc
      (2 : ℤ) ^ j * y + 2 ^ j * x = 2 ^ j * (x + y) := by ring
      _ = (2 ^ j * 2) * t := by rw [← ht]; ring
  · obtain ⟨p, hp, hcut⟩ := hleft
    exact ⟨p, List.mem_cons_of_mem _ hp, hcut⟩
  · obtain ⟨p, hp, hcut⟩ := hright
    exact ⟨p, List.mem_cons_of_mem _ hp, hcut⟩

theorem dyadicMean_midpointClosure {S : ℕ → Finset ℤ} {cut : ℤ} {j : ℕ}
    {T : Finset ℤ} (hT : ∀ x ∈ T, DyadicMean S cut j x) :
    ∀ x ∈ midpointClosure T (S j), DyadicMean S cut (j + 1) x := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxT | hxMid
  · exact (hT x hxT).carry
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxMid
    obtain ⟨hp, heven⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpT, hpS⟩ := Finset.mem_product.mp hp
    exact (hT p.1 hpT).midpoint hpS (by omega)

theorem dyadic_list_length_le {L : List (ℕ × ℤ)} {a j : ℕ}
    (hlevel : ∀ p ∈ L, a ≤ p.1) (hweight : (L.map levelWeight).sum = 2 ^ j)
    (haj : a ≤ j) : L.length ≤ 2 ^ (j - a) := by
  have hsum : L.length * 2 ^ a ≤ (L.map levelWeight).sum := by
    calc
      L.length * 2 ^ a = (L.map fun _ => 2 ^ a).sum := by simp
      _ ≤ (L.map levelWeight).sum := by
        apply List.sum_le_sum
        intro p hp
        exact Nat.pow_le_pow_right Nat.zero_lt_two (hlevel p hp)
  rw [hweight] at hsum
  have hsplit : (2 : ℕ) ^ j = 2 ^ (j - a) * 2 ^ a := by
    rw [← pow_add, Nat.sub_add_cancel haj]
  rw [hsplit] at hsum
  exact Nat.le_of_mul_le_mul_right hsum (Nat.two_pow_pos a)

end Erdos790.Upper
