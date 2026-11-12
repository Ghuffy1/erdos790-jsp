import Erdos790.Upper.DenseSeed

/-!
# A dense earlier coordinate union supplies a persistent lattice core
-/

namespace Erdos790.Upper

theorem dense_seed_lattice_room {η : ℝ} {g W M : ℕ}
    (hη : 0 < η) (hηone : η ≤ 1) (hg : η * g ≤ 2)
    (hwidth : η * M / 2 ≤ W) (hlarge : 64 ≤ η ^ 2 * M) :
    8 * g + 8 ≤ W := by
  have hscaled := mul_le_mul_of_nonneg_left hwidth hη.le
  have hbound : η * (8 * (g : ℝ) + 8) ≤ η * W := by nlinarith
  have hreal : 8 * (g : ℝ) + 8 ≤ W := (mul_le_mul_iff_of_pos_left hη).mp hbound
  exact_mod_cast hreal

theorem seed_core_of_central_means {S : ℕ → Finset ℤ} {cut u : ℤ}
    {j g W M : ℕ} {η : ℝ} (hg : 0 < g) (hWpos : 0 < W)
    (hroom : 8 * g + 8 ≤ W) (hwidth : η * M / 2 ≤ W)
    (hmean : ∀ t : ℤ, (W : ℤ) ≤ 4 * (t - u) → 4 * (t - u) ≤ 3 * (W : ℤ) →
      (g : ℤ) ∣ t - u → DyadicMean S cut j t) :
    ∃ p q : ℤ, (g : ℤ) ∣ p - u ∧ (g : ℤ) ∣ q - u ∧
      u ≤ p ∧ q ≤ u + W ∧ p ≤ q ∧ η * M / 8 ≤ ((q - p : ℤ) : ℝ) ∧
      ∀ t : ℤ, p ≤ t → t ≤ q → (g : ℤ) ∣ t - u → DyadicMean S cut j t := by
  obtain ⟨p, q, hp, hq, hpu, hqu, hleft, hright, hspan⟩ :=
    central_lattice_interval (g := (g : ℤ)) (u := u) (p := u) (q := u + W)
      (by exact_mod_cast hg)
      (by have h : 8 * (g : ℤ) + 8 ≤ W := by exact_mod_cast hroom
          omega)
  have hspanInt : (W : ℤ) ≤ 4 * (q - p) := by omega
  have hspanReal : (W : ℝ) ≤ 4 * ((q - p : ℤ) : ℝ) := by exact_mod_cast hspanInt
  refine ⟨p, q, hp, hq, hpu, hqu, ?_, by linarith, ?_⟩
  · have hWint : (0 : ℤ) < W := by exact_mod_cast hWpos
    omega
  · intro t hpt htq htclass
    apply hmean t (by omega) (by omega) htclass

theorem dense_coordinate_seed_core {S : ℕ → Finset ℤ} {A : Finset ℤ}
    {cut u c : ℤ} {a n W M cLevel : ℕ} {η : ℝ}
    (hu : u ∈ A) (hv : u + (W : ℤ) ∈ A)
    (hA : ∀ t ∈ A, u ≤ t ∧ t ≤ u + W)
    (hη : 0 < η) (hηone : η ≤ 1) (hsize : 2 ≤ η * M)
    (hdensity : η * M ≤ A.card) (hWM : W ≤ M)
    (hlarge : 64 ≤ η ^ 2 * M) (hbudget : 100 ≤ η ^ 2 * (2 : ℝ) ^ n) (hn : 0 < n)
    (hseen : ∀ t ∈ A, ∃ k ≤ a, t ∈ S k)
    (hcLevel : cLevel ≤ a) (hc : c ∈ S cLevel)
    (hside : (c < cut ∧ ∀ t ∈ A, cut ≤ t) ∨ (cut ≤ c ∧ ∀ t ∈ A, t < cut))
    (hcRange : |c - u| ≤ 2 * (M : ℤ)) :
    ∃ g : ℕ, 0 < g ∧ η * g ≤ 2 ∧ ∃ p q : ℤ,
      (g : ℤ) ∣ p - u ∧ (g : ℤ) ∣ q - u ∧
      u ≤ p ∧ q ≤ u + W ∧ p ≤ q ∧ η * M / 8 ≤ ((q - p : ℤ) : ℝ) ∧
      ∀ t : ℤ, p ≤ t → t ≤ q → (g : ℤ) ∣ t - u → DyadicMean S cut (a + n) t := by
  classical
  let D := coordinateDifferences A u
  have hlow : ∀ t ∈ A, u ≤ t := fun t ht => (hA t ht).1
  have hmem : ∀ d : ℕ, d ∈ D ↔ u + (d : ℤ) ∈ A := fun _ => coordinateDifferences_mem_iff hlow
  have hzero : 0 ∈ D := (hmem 0).mpr (by simpa only [Nat.cast_zero, add_zero] using hu)
  have hW : W ∈ D := (hmem W).mpr hv
  have hD : ∀ d ∈ D, d ≤ W := by
    intro d hd
    have h := (hA _ ((hmem d).mp hd)).2
    exact_mod_cast (show (d : ℤ) ≤ W by omega)
  have hcard : D.card = A.card := coordinateDifferences_card A u hlow
  have hDensity : η * M ≤ D.card := by simpa only [hcard] using hdensity
  have hwidth := density_width_bound hD hsize hDensity
  have hWpos : 0 < W := by
    have hreal : (1 : ℝ) ≤ W := by linarith
    have hnat : 1 ≤ W := by exact_mod_cast hreal
    omega
  obtain ⟨g, K, hg, hgcd, hK, hgBound, hKBound, _⟩ :=
    dense_seed_parameters hWpos hW hD hηone hsize hDensity hWM
  have hselected : ∀ d ∈ D, ∃ k ≤ a, u + (d : ℤ) ∈ S k :=
    fun d hd => hseen _ ((hmem d).mp hd)
  let level (d : ℕ) : ℕ := if hd : d ∈ D then Classical.choose (hselected d hd) else 0
  have hlevel : ∀ d ∈ D, level d ≤ a ∧ u + (d : ℤ) ∈ S (level d) := by
    intro d hd
    simpa only [level, dif_pos hd] using Classical.choose_spec (hselected d hd)
  have hsideD : (c < cut ∧ ∀ d ∈ D, cut ≤ u + (d : ℤ)) ∨
      (cut ≤ c ∧ ∀ d ∈ D, u + (d : ℤ) < cut) := by
    rcases hside with ⟨hleft, hAleft⟩ | ⟨hright, hAright⟩
    · exact Or.inl ⟨hleft, fun d hd => hAleft _ ((hmem d).mp hd)⟩
    · exact Or.inr ⟨hright, fun d hd => hAright _ ((hmem d).mp hd)⟩
  refine ⟨g, hg, hgBound, ?_⟩
  apply seed_core_of_central_means hg hWpos
    (dense_seed_lattice_room hη hηone hgBound hwidth hlarge) hwidth
  intro t htLower htUpper htclass
  exact dense_dyadic_seed level hWpos hzero hW hD hK hg hgcd hη hηone hwidth hWM
    hgBound hKBound hbudget hn hcLevel hc hlevel hsideD hcRange htLower htUpper htclass

end Erdos790.Upper
