import Erdos790.Upper.AffineProgressions

/-!
# The finite Varnavides estimate and abundant centered pairs
-/

open Finset

namespace Erdos790.Upper

theorem affineProgressions_card_le (S : Finset ℤ) (N M D : ℕ) :
    (affineProgressions S N M D).card ≤ (progressionPairs S).card * M ^ 2 := by
  classical
  let f : ((ℤ × ℕ) × (ℕ × ℕ)) → ((ℤ × ℤ) × (ℕ × ℕ)) := fun p =>
    ((p.1.1 + (p.2.1 : ℤ) * p.1.2, p.1.1 + (p.2.2 : ℤ) * p.1.2), p.2)
  let target := progressionPairs S ×ˢ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M)
  have hmap : Set.MapsTo f (affineProgressions S N M D) target := by
    intro p hp
    obtain ⟨hpbase, hpAP⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hpindices⟩ := Finset.mem_product.mp hpbase
    obtain ⟨hpPair, _, y, hy, heq⟩ := Finset.mem_filter.mp hpAP
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hpPair
    have hx := (Finset.mem_filter.mp hi).2
    have hz := (Finset.mem_filter.mp hj).2
    have hyS := (Finset.mem_filter.mp hy).2
    have heqInt : (p.2.1 : ℤ) + y = 2 * p.2.2 := by exact_mod_cast heq
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hz⟩, ?_⟩, hpindices⟩
    dsimp [f]
    have hvalue : 2 * (p.1.1 + (p.2.2 : ℤ) * p.1.2) -
        (p.1.1 + (p.2.1 : ℤ) * p.1.2) = p.1.1 + (y : ℤ) * p.1.2 := by
      nlinarith
    rwa [hvalue]
  have hinj : (affineProgressions S N M D : Set ((ℤ × ℕ) × (ℕ × ℕ))).InjOn f := by
    rintro ⟨⟨a, q⟩, ⟨i, j⟩⟩ hp ⟨⟨b, r⟩, ⟨i', j'⟩⟩ hr heq
    have hi := congrArg (fun z : (ℤ × ℤ) × (ℕ × ℕ) => z.2.1) heq
    have hj := congrArg (fun z : (ℤ × ℤ) × (ℕ × ℕ) => z.2.2) heq
    dsimp [f] at hi hj
    subst i'
    subst j'
    have hx := congrArg (fun z : (ℤ × ℤ) × (ℕ × ℕ) => z.1.1) heq
    have hz := congrArg (fun z : (ℤ × ℤ) × (ℕ × ℕ) => z.1.2) heq
    dsimp [f] at hx hz
    have hij : i < j := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2).2.1
    have hne : (j : ℤ) - i ≠ 0 := by omega
    have hdiff : ((j : ℤ) - i) * q = ((j : ℤ) - i) * r := by nlinarith
    have hqr : q = r := by exact_mod_cast (mul_left_cancel₀ hne hdiff)
    subst r
    have hab : a = b := by omega
    subst b
    rfl
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  simpa only [target, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel,
    ← pow_two] using hcard

theorem affineParameters_card (N D : ℕ) :
    (affineParameters N D).card = (2 * N + 1) * D := by
  have hinterval : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    omega
  simp only [affineParameters, Finset.card_product, hinterval, Nat.card_Icc,
    Nat.add_sub_cancel]

theorem finite_varnavides {S : Finset ℤ} {N M D k : ℕ}
    (hS : S ⊆ Finset.Icc 1 (N : ℤ)) (hMD : M * D ≤ N)
    (hbound : ThreeTermExtremalBound M k) :
    S.card * M * D ≤ (2 * N + 1) * D * k + (progressionPairs S).card * M ^ 2 := by
  classical
  have hlocal : ∀ p ∈ affineParameters N D,
      (affineIndexSet S M p.1 p.2).card ≤ k +
        (natProgressionPairs (affineIndexSet S M p.1 p.2)).card := by
    intro p hp
    exact cardinal_le_extremal_add_pairs hbound (Finset.filter_subset _ _)
  have hsum := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  rw [← affineIncidences_card_sum, affineIncidences_card hS hMD,
    ← affineProgressions_card_sum, affineParameters_card] at hsum
  exact hsum.trans (Nat.add_le_add_left (affineProgressions_card_le S N M D) _)

theorem centerRich_of_extremal_bound {N M D L R k : ℕ}
    (hM : 0 < M) (hD : 0 < D) (hL : 0 < L) (hN : N = M * D)
    (hsmall : 8 * L * k ≤ M) (hscale : 2 * (R + 1) * M ≤ D)
    (hbound : ThreeTermExtremalBound M k) :
    CenterRich R (N / L) (Finset.Icc 1 (N : ℤ)) := by
  intro S hS hlarge
  by_contra hnone
  push Not at hnone
  have hNpos : 0 < N := by rw [hN]; positivity
  have hSpos : 0 < S.card := (Nat.zero_le (N / L)).trans_lt hlarge
  have hNL : N ≤ L * S.card := by
    have hmod := Nat.mod_lt N hL
    have hdiv := Nat.div_add_mod N L
    nlinarith
  have hI := finite_varnavides hS (by omega : M * D ≤ N) hbound
  have hAP := progressionPairs_card_le_of_no_good hnone
  have hupper : S.card * M * D ≤
      (2 * N + 1) * D * k + (R + 1) * S.card * M ^ 2 :=
    hI.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (M ^ 2) hAP) _)
  have hfirst : 8 * ((2 * N + 1) * D * k) ≤ 3 * (S.card * M * D) := by
    calc
      _ ≤ 8 * ((3 * N) * D * k) := by gcongr; omega
      _ ≤ 8 * ((3 * (L * S.card)) * D * k) := by gcongr
      _ = (3 * S.card * D) * (8 * L * k) := by ring
      _ ≤ (3 * S.card * D) * M := Nat.mul_le_mul_left _ hsmall
      _ = _ := by ring
  have hsecond : 8 * ((R + 1) * S.card * M ^ 2) ≤ 4 * (S.card * M * D) := by
    calc
      _ = (4 * S.card * M) * (2 * (R + 1) * M) := by ring
      _ ≤ (4 * S.card * M) * D := Nat.mul_le_mul_left _ hscale
      _ = _ := by ring
  have hpositive : 0 < S.card * M * D := by positivity
  nlinarith

end Erdos790.Upper
