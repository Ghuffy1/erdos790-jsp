import Erdos790.Upper.CyclicSums
import Erdos790.Upper.DyadicCombinations
import Erdos790.Upper.LatticeSums

/-!
# Seeding a lattice of exact mixed means

The finite-group sum theorem supplies the later-side terms. Copies of one
opposite-side point then make every admissible target a mixed dyadic mean.
-/

namespace Erdos790.Upper

theorem dyadicMean_seed {S : ℕ → Finset ℤ} {D : Finset ℕ}
    {cut u c t : ℤ} {a n g W K cLevel : ℕ} (level : ℕ → ℕ)
    (hWpos : 0 < W) (hzero : 0 ∈ D) (hW : W ∈ D)
    (hD : ∀ d ∈ D, d ≤ W) (hlarge : 2 * W ≤ K * (D.card - 1))
    (hg : 0 < g) (hgcd : (D.image (fun d : ℕ => (d : ℤ))).gcd id = (g : ℤ))
    (hn : 0 < n) (hgpow : g < 2 ^ n)
    (hcLevel : cLevel ≤ a) (hc : c ∈ S cLevel)
    (hselected : ∀ d ∈ D, level d ≤ a ∧ u + d ∈ S (level d))
    (hside : (c < cut ∧ ∀ d ∈ D, cut ≤ u + d) ∨
      (cut ≤ c ∧ ∀ d ∈ D, u + d < cut))
    (hclass : (g : ℤ) ∣ t - u)
    (hlower : ((K * W : ℕ) : ℤ) ≤
      (2 : ℤ) ^ n * (t - u) - g * (c - u))
    (hupper : (2 : ℤ) ^ n * (t - u) - g * (c - u) ≤
      (((2 ^ n - g - K) * W : ℕ) : ℤ)) :
    DyadicMean S cut (a + n) t := by
  let N : ℤ := (2 : ℤ) ^ n * (t - u) - g * (c - u)
  have hNnonneg : 0 ≤ N := (Int.natCast_nonneg (K * W)).trans hlower
  have hcastN : (N.toNat : ℤ) = N := Int.toNat_of_nonneg hNnonneg
  have hdiv : (D.image (fun d : ℕ => (d : ℤ))).gcd id ∣ (N.toNat : ℤ) := by
    rw [hgcd, hcastN]
    exact dvd_sub (dvd_mul_of_dvd_right hclass _) (dvd_mul_right _ _)
  have hNlower : K * W ≤ N.toNat := by
    have h := hlower
    change ((K * W : ℕ) : ℤ) ≤ N at h
    rw [← hcastN] at h
    exact_mod_cast h
  have hNupper : N.toNat ≤ (2 ^ n - g - K) * W := by
    have h := hupper
    change N ≤ (((2 ^ n - g - K) * W : ℕ) : ℤ) at h
    rw [← hcastN] at h
    exact_mod_cast h
  obtain ⟨Q, hQ, hlength, hsum⟩ := exact_length_sum_of_gcd_dvd hWpos hzero hW
    hD hlarge hdiv hNlower hNupper
  have hcount : Q.length + g = 2 ^ n := by rw [hlength]; omega
  have hQnonempty : Q ≠ [] := by
    intro heq
    rw [heq, List.length_nil] at hlength
    omega
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil Q hQnonempty
  let raw := Q.map (fun d : ℕ => (level d, u + (d : ℤ))) ++
    List.replicate g (cLevel, c)
  have hraw : ∀ p ∈ raw, p.1 ≤ a ∧ p.2 ∈ S p.1 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
      exact hselected e (hQ e he)
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hp
      exact ⟨hcLevel, hc⟩
  have hrawCount : raw.length = 2 ^ n := by
    simpa only [raw, List.length_append, List.length_map, List.length_replicate] using hcount
  have hcastLength : (Q.length : ℤ) = (2 : ℤ) ^ n - g := by
    have h : (Q.length : ℤ) + g = (2 : ℤ) ^ n := by exact_mod_cast hcount
    omega
  have hcastSum : (Q.sum : ℤ) = N := by rw [hsum, hcastN]
  have hrawSum : (raw.map Prod.snd).sum = (2 : ℤ) ^ n * t := by
    have hshift : (Q.map (fun d : ℕ => u + (d : ℤ))).sum =
        Q.length * u + (Q.sum : ℤ) := by
      simpa only [one_mul] using sum_map_nat_affine Q u 1
    simp only [raw, List.map_append, List.map_map, Function.comp_def,
      List.map_replicate, List.sum_append, List.sum_replicate, Int.nsmul_eq_mul]
    change (Q.map (fun d : ℕ => u + (d : ℤ))).sum + g * c = _
    rw [hshift, hcastLength, hcastSum]
    dsimp [N]
    ring
  have hcRaw : (cLevel, c) ∈ raw :=
    List.mem_append.mpr (Or.inr (List.mem_replicate.mpr ⟨ne_of_gt hg, rfl⟩))
  have hdRaw : (level d, u + (d : ℤ)) ∈ raw :=
    List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨d, hd, rfl⟩))
  apply dyadicMean_of_selected_list raw hn hraw hrawCount hrawSum
  · rcases hside with ⟨hcleft, _⟩ | ⟨_, hdleft⟩
    · exact ⟨(cLevel, c), hcRaw, hcleft⟩
    · exact ⟨(level d, u + (d : ℤ)), hdRaw, hdleft d (hQ d hd)⟩
  · rcases hside with ⟨_, hdright⟩ | ⟨hcright, _⟩
    · exact ⟨(level d, u + (d : ℤ)), hdRaw, hdright d (hQ d hd)⟩
    · exact ⟨(cLevel, c), hcRaw, hcright⟩

end Erdos790.Upper
