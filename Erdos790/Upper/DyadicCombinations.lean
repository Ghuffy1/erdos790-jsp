import Erdos790.Upper.DyadicMeans

/-!
# Combining exact dyadic means

Lists retain multiplicity throughout. Concatenating their witnesses records
the exact dyadic weights and preserves the occurrence of both sides of a cut.
-/

namespace Erdos790.Upper

theorem dyadicMean_list_witness {S : ℕ → Finset ℤ} {cut : ℤ} {j : ℕ}
    (L : List ℤ) (hL : ∀ x ∈ L, DyadicMean S cut j x) :
    ∃ K : List (ℕ × ℤ),
      (∀ p ∈ K, p.1 < j ∧ p.2 ∈ S p.1) ∧
      (K.map levelWeight).sum = L.length * 2 ^ j ∧
      (K.map levelMoment).sum = (2 : ℤ) ^ j * L.sum ∧
      (L ≠ [] → ∃ p ∈ K, p.2 < cut) ∧
      (L ≠ [] → ∃ p ∈ K, cut ≤ p.2) := by
  induction L with
  | nil =>
    exact ⟨[], by simp, by simp, by simp, by simp, by simp⟩
  | cons x L ih =>
    obtain ⟨Kx, hx, hxw, hxm, hxl, hxr⟩ := hL x (by simp)
    obtain ⟨K, hK, hKw, hKm, _, _⟩ := ih (fun y hy => hL y (by simp [hy]))
    refine ⟨Kx ++ K, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hx p hp
      · exact hK p hp
    · simp only [List.map_append, List.sum_append, hxw, hKw, List.length_cons]
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    · simp only [List.map_append, List.sum_append, hxm, hKm, List.sum_cons]
      ring
    · intro _
      obtain ⟨p, hp, hc⟩ := hxl
      exact ⟨p, List.mem_append.mpr (Or.inl hp), hc⟩
    · intro _
      obtain ⟨p, hp, hc⟩ := hxr
      exact ⟨p, List.mem_append.mpr (Or.inl hp), hc⟩

theorem DyadicMean.combine {S : ℕ → Finset ℤ} {cut b t : ℤ} {j n v : ℕ}
    {L : List ℤ} (hn : 0 < n) (hne : L ≠ [])
    (hL : ∀ x ∈ L, DyadicMean S cut j x)
    (hb : 0 < v → b ∈ S j) (hcount : L.length + v = 2 ^ n)
    (hsum : L.sum + v * b = (2 : ℤ) ^ n * t) :
    DyadicMean S cut (j + n) t := by
  obtain ⟨K, hK, hw, hm, hl, hr⟩ := dyadicMean_list_witness L hL
  refine ⟨K ++ List.replicate v (j, b), ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨by have := (hK p hp).1; omega, (hK p hp).2⟩
    · obtain ⟨hv, rfl⟩ := List.mem_replicate.mp hp
      exact ⟨by omega, hb (by omega)⟩
  · simp only [List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, levelWeight, hw, Nat.nsmul_eq_mul]
    rw [← Nat.add_mul, hcount, pow_add]
    exact Nat.mul_comm _ _
  · simp only [List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, levelMoment, hm, Int.nsmul_eq_mul]
    calc
      (2 : ℤ) ^ j * L.sum + v * (2 ^ j * b) =
          2 ^ j * (L.sum + v * b) := by ring
      _ = 2 ^ j * (2 ^ n * t) := by rw [hsum]
      _ = 2 ^ (j + n) * t := by rw [pow_add]; ring
  · obtain ⟨p, hp, hc⟩ := hl hne
    exact ⟨p, List.mem_append.mpr (Or.inl hp), hc⟩
  · obtain ⟨p, hp, hc⟩ := hr hne
    exact ⟨p, List.mem_append.mpr (Or.inl hp), hc⟩

def liftLevelSamples (a : ℕ) (L : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  L.flatMap fun p => List.replicate (2 ^ (a - p.1)) p

theorem mem_liftLevelSamples {a : ℕ} {L : List (ℕ × ℤ)} {p : ℕ × ℤ} :
    p ∈ liftLevelSamples a L ↔ p ∈ L := by
  simp only [liftLevelSamples, List.mem_flatMap, List.mem_replicate]
  constructor
  · rintro ⟨q, hq, _, rfl⟩
    exact hq
  · intro hp
    exact ⟨p, hp, ne_of_gt (Nat.two_pow_pos _), rfl⟩

theorem liftLevelSamples_weight (a : ℕ) (L : List (ℕ × ℤ))
    (hL : ∀ p ∈ L, p.1 ≤ a) :
    ((liftLevelSamples a L).map levelWeight).sum = L.length * 2 ^ a := by
  induction L with
  | nil => simp [liftLevelSamples]
  | cons p L ih =>
    have hp := hL p (by simp)
    have ht := ih (fun q hq => hL q (by simp [hq]))
    simp only [liftLevelSamples] at ht
    simp only [liftLevelSamples, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate, levelWeight, Nat.nsmul_eq_mul,
      ht, List.length_cons]
    rw [← pow_add, Nat.sub_add_cancel hp]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem liftLevelSamples_moment (a : ℕ) (L : List (ℕ × ℤ))
    (hL : ∀ p ∈ L, p.1 ≤ a) :
    ((liftLevelSamples a L).map levelMoment).sum =
      (2 : ℤ) ^ a * (L.map Prod.snd).sum := by
  induction L with
  | nil => simp [liftLevelSamples]
  | cons p L ih =>
    have hp := hL p (by simp)
    have ht := ih (fun q hq => hL q (by simp [hq]))
    simp only [liftLevelSamples] at ht
    simp only [liftLevelSamples, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate, levelMoment, Int.nsmul_eq_mul,
      ht, List.map_cons, List.sum_cons, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hp]
    ring

theorem dyadicMean_of_selected_list {S : ℕ → Finset ℤ} {cut t : ℤ} {a n : ℕ}
    (L : List (ℕ × ℤ)) (hn : 0 < n)
    (hL : ∀ p ∈ L, p.1 ≤ a ∧ p.2 ∈ S p.1)
    (hcount : L.length = 2 ^ n)
    (hsum : (L.map Prod.snd).sum = (2 : ℤ) ^ n * t)
    (hleft : ∃ p ∈ L, p.2 < cut) (hright : ∃ p ∈ L, cut ≤ p.2) :
    DyadicMean S cut (a + n) t := by
  refine ⟨liftLevelSamples a L, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have h := hL p (mem_liftLevelSamples.mp hp)
    exact ⟨by omega, h.2⟩
  · rw [liftLevelSamples_weight a L (fun p hp => (hL p hp).1), hcount, pow_add]
    exact Nat.mul_comm _ _
  · rw [liftLevelSamples_moment a L (fun p hp => (hL p hp).1), hsum, pow_add]
    ring
  · obtain ⟨p, hp, hc⟩ := hleft
    exact ⟨p, mem_liftLevelSamples.mpr hp, hc⟩
  · obtain ⟨p, hp, hc⟩ := hright
    exact ⟨p, mem_liftLevelSamples.mpr hp, hc⟩

end Erdos790.Upper
