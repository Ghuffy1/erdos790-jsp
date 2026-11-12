import Erdos790.Upper.LatticeSeed
import Erdos790.Upper.LatticeIntervals
import Erdos790.Upper.DigitPacking
import Erdos790.Upper.SeedBounds

/-!
# From a dense coordinate set to an interval of exact mixed means
-/

namespace Erdos790.Upper

def coordinateDifferences (A : Finset ℤ) (u : ℤ) : Finset ℕ :=
  A.image (fun t => (t - u).toNat)

theorem coordinateDifferences_mem_iff {A : Finset ℤ} {u : ℤ} {d : ℕ}
    (hlower : ∀ t ∈ A, u ≤ t) : d ∈ coordinateDifferences A u ↔ u + d ∈ A := by
  constructor
  · intro hd
    obtain ⟨t, ht, htd⟩ := Finset.mem_image.mp hd
    have hcast := Int.toNat_of_nonneg (sub_nonneg.mpr (hlower t ht))
    have heq : u + (d : ℤ) = t := by rw [← htd, hcast]; omega
    exact heq ▸ ht
  · intro ht
    refine Finset.mem_image.mpr ⟨u + d, ht, ?_⟩
    simp

theorem coordinateDifferences_card (A : Finset ℤ) (u : ℤ)
    (hlower : ∀ t ∈ A, u ≤ t) : (coordinateDifferences A u).card = A.card := by
  apply Finset.card_image_of_injOn
  intro s hs t ht heq
  have hscast := Int.toNat_of_nonneg (sub_nonneg.mpr (hlower s hs))
  have htcast := Int.toNat_of_nonneg (sub_nonneg.mpr (hlower t ht))
  have heqcast := congrArg (fun n : ℕ => (n : ℤ)) heq
  rw [hscast, htcast] at heqcast
  omega

theorem positive_difference_gcd {D : Finset ℕ} {W : ℕ}
    (hWpos : 0 < W) (hW : W ∈ D) :
    ∃ g : ℕ, 0 < g ∧ (D.image (fun d : ℕ => (d : ℤ))).gcd id = (g : ℤ) ∧
      ∀ d ∈ D, g ∣ d := by
  let G := (D.image (fun d : ℕ => (d : ℤ))).gcd id
  have hnonneg : 0 ≤ G := Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  have hne : G ≠ 0 := by
    intro hz
    have hzero := Finset.gcd_eq_zero_iff.mp hz (W : ℤ)
      (Finset.mem_image.mpr ⟨W, hW, rfl⟩)
    simp only [id_eq, Nat.cast_eq_zero] at hzero
    omega
  have hpos : 0 < G := lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hcast : (G.toNat : ℤ) = G := Int.toNat_of_nonneg hnonneg
  refine ⟨G.toNat, by omega, hcast.symm, ?_⟩
  intro d hd
  have hdiv : G ∣ (d : ℤ) := Finset.gcd_dvd (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
  rw [← hcast] at hdiv
  exact_mod_cast hdiv

theorem dense_seed_parameters {D : Finset ℕ} {W M : ℕ} {η : ℝ}
    (hWpos : 0 < W) (hW : W ∈ D) (hD : ∀ d ∈ D, d ≤ W)
    (hηone : η ≤ 1) (hsize : 2 ≤ η * M) (hdensity : η * M ≤ D.card) (hWM : W ≤ M) :
    ∃ g K : ℕ, 0 < g ∧ (D.image (fun d : ℕ => (d : ℤ))).gcd id = (g : ℤ) ∧
      2 * W ≤ K * (D.card - 1) ∧ η * g ≤ 2 ∧ η * K ≤ 5 ∧ η * M / 2 ≤ W := by
  obtain ⟨g, hg, hgcd, hdiv⟩ := positive_difference_gcd hWpos hW
  have hcard : 2 ≤ D.card := by exact_mod_cast hsize.trans hdensity
  refine ⟨g, 2 * W / (D.card - 1) + 1, hg, hgcd, residue_parameter_covers hcard,
    density_divisor_bound hD hdiv hsize hdensity hWM,
    density_residue_parameter_bound hηone hsize hdensity hWM,
    density_width_bound hD hsize hdensity⟩

theorem dense_dyadic_seed {S : ℕ → Finset ℤ} {D : Finset ℕ}
    {cut u c t : ℤ} {a n g W K M cLevel : ℕ} {η : ℝ} (level : ℕ → ℕ)
    (hWpos : 0 < W) (hzero : 0 ∈ D) (hW : W ∈ D)
    (hD : ∀ d ∈ D, d ≤ W) (hlarge : 2 * W ≤ K * (D.card - 1))
    (hg : 0 < g) (hgcd : (D.image (fun d : ℕ => (d : ℤ))).gcd id = (g : ℤ))
    (hη : 0 < η) (hηone : η ≤ 1) (hwidth : η * M / 2 ≤ W) (hWM : W ≤ M)
    (hgBound : η * g ≤ 2) (hKBound : η * K ≤ 5)
    (hbudget : 100 ≤ η ^ 2 * (2 : ℝ) ^ n) (hn : 0 < n)
    (hcLevel : cLevel ≤ a) (hc : c ∈ S cLevel)
    (hselected : ∀ d ∈ D, level d ≤ a ∧ u + d ∈ S (level d))
    (hside : (c < cut ∧ ∀ d ∈ D, cut ≤ u + d) ∨
      (cut ≤ c ∧ ∀ d ∈ D, u + d < cut))
    (hcRange : |c - u| ≤ 2 * (M : ℤ))
    (htLower : (W : ℤ) ≤ 4 * (t - u))
    (htUpper : 4 * (t - u) ≤ 3 * (W : ℤ))
    (hclass : (g : ℤ) ∣ t - u) : DyadicMean S cut (a + n) t := by
  have hpower := seed_power_room hη hηone hgBound hKBound hbudget
  have hwindow := seed_window_bounds hη (by positivity : (0 : ℝ) ≤ M) hwidth
    (by exact_mod_cast hWM) (by positivity : (0 : ℝ) ≤ g)
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n) hgBound hKBound hbudget
    (x := ((t - u : ℤ) : ℝ)) (c := ((c - u : ℤ) : ℝ))
    (by have h : (W : ℝ) ≤ 4 * ((t - u : ℤ) : ℝ) := by exact_mod_cast htLower
        linarith)
    (by have h : 4 * ((t - u : ℤ) : ℝ) ≤ 3 * (W : ℝ) := by exact_mod_cast htUpper
        linarith)
    (by exact_mod_cast hcRange)
  have hlower : ((K * W : ℕ) : ℤ) ≤ (2 : ℤ) ^ n * (t - u) - g * (c - u) := by
    exact_mod_cast hwindow.1
  have hcount : g + K ≤ 2 ^ n := hpower.le
  have hgPower : g ≤ 2 ^ n := by omega
  have hKPower : K ≤ 2 ^ n - g := by omega
  have hupperReal : (2 : ℝ) ^ n * ((t - u : ℤ) : ℝ) - g * ((c - u : ℤ) : ℝ) ≤
      ((2 ^ n - g - K : ℕ) : ℝ) * W := by
    simpa only [Nat.cast_sub hKPower, Nat.cast_sub hgPower,
      Nat.cast_pow, Nat.cast_ofNat] using hwindow.2
  have hupper : (2 : ℤ) ^ n * (t - u) - g * (c - u) ≤
      (((2 ^ n - g - K) * W : ℕ) : ℤ) := by exact_mod_cast hupperReal
  exact dyadicMean_seed level hWpos hzero hW hD hlarge hg hgcd hn (by omega)
    hcLevel hc hselected hside hclass hlower hupper

end Erdos790.Upper
