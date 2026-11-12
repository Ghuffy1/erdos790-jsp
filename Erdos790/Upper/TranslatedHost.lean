import Erdos790.Upper.SpectralSumCover
import Erdos790.Upper.RepeatedLists
import Mathlib.Combinatorics.Pigeonhole

/-!
# Integer hosts assembled from translated offset fibers
-/

namespace Erdos790.Upper

def translatedHost {J : ℕ} (X : ℕ) (offset : Fin J → ℕ) (translations : Finset ℕ) :
    Finset ℕ :=
  Finset.univ.image (fun p : Fin J × ↥translations => X + offset p.1 + p.2.val)

theorem translatedHost_injective {J Q X : ℕ} (offset : Fin J → ℕ)
    (translations : Finset ℕ) (hX : Q ∣ X) (hz : ∀ z ∈ translations, Q ∣ z)
    (hinjective : Function.Injective (fun i => offset i % Q)) :
    Function.Injective (fun p : Fin J × ↥translations => X + offset p.1 + p.2.val) := by
  intro a b hab
  have ha : (X + offset a.1 + a.2.val) % Q = offset a.1 % Q := by
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hX,
      Nat.mod_eq_zero_of_dvd (hz a.2.val a.2.property)]
  have hb : (X + offset b.1 + b.2.val) % Q = offset b.1 % Q := by
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hX,
      Nat.mod_eq_zero_of_dvd (hz b.2.val b.2.property)]
  have hi : a.1 = b.1 := hinjective (ha.symm.trans ((congrArg (fun x => x % Q) hab).trans hb))
  apply Prod.ext hi
  apply Subtype.ext
  change X + offset a.1 + a.2.val = X + offset b.1 + b.2.val at hab
  rw [hi] at hab
  omega

theorem translatedHost_card {J Q X : ℕ} (offset : Fin J → ℕ)
    (translations : Finset ℕ) (hX : Q ∣ X) (hz : ∀ z ∈ translations, Q ∣ z)
    (hinjective : Function.Injective (fun i => offset i % Q)) :
    (translatedHost X offset translations).card = J * translations.card := by
  rw [translatedHost, Finset.card_image_of_injective _
    (translatedHost_injective offset translations hX hz hinjective)]
  simp

theorem translatedHost_bounds {J X N : ℕ} (offset : Fin J → ℕ)
    (translations : Finset ℕ) (hX : X = 4 * N)
    (hoffset : ∀ i, offset i < N) (hz : ∀ z ∈ translations, z < N)
    {a : ℕ} (ha : a ∈ translatedHost X offset translations) :
    X ≤ a ∧ a < 2 * X := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
  have ho := hoffset p.1
  have ht := hz p.2.val p.2.property
  omega

theorem translatedHost_coprime {J Q X : ℕ} (offset : Fin J → ℕ)
    (translations : Finset ℕ) (hX : Q ∣ X) (hz : ∀ z ∈ translations, Q ∣ z)
    (hoffset : ∀ i, Nat.Coprime (offset i) Q)
    {a : ℕ} (ha : a ∈ translatedHost X offset translations) : Nat.Coprime a Q := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
  apply (Nat.add_coprime_iff_left (hz p.2.val p.2.property)).mpr
  exact (Nat.add_coprime_iff_right hX).mpr (hoffset p.1)

theorem geometric_tail_of_sample_budget {M S : ℝ} {k : ℕ} (hM : 0 ≤ M)
    (hMS : M ≤ S) (hbudget : S * Real.exp (-(k : ℝ) / 2) ≤ 1 / 2) :
    M * (1 / 200 : ℝ) ^ k < 1 := by
  have hsingle : (1 / 200 : ℝ) ≤ Real.exp (-1 / 2) := by
    have h := Real.add_one_le_exp (-1 / 2)
    linarith
  have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 200) hsingle k
  have hexp : (Real.exp (-1 / 2)) ^ k = Real.exp (-(k : ℝ) / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hpower
  calc
    M * (1 / 200 : ℝ) ^ k ≤ M * Real.exp (-(k : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hpower hM
    _ ≤ S * Real.exp (-(k : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hMS (Real.exp_pos _).le
    _ ≤ 1 / 2 := hbudget
    _ < 1 := by norm_num

end Erdos790.Upper
