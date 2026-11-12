import Erdos790.Upper.LatticePropagation
import Erdos790.Upper.SeedParameters

/-!
# Integer coordinates for selected points and lattice cores
-/

namespace Erdos790.Upper

theorem ediv_interval_width {x y g : ℤ} (hg : 0 < g) (hxy : x ≤ y) :
    y / g - x / g ≤ y - x := by
  have hx := Int.emod_add_mul_ediv x g
  have hy := Int.emod_add_mul_ediv y g
  have hxr := Int.emod_lt_of_pos x hg
  have hyr := Int.emod_nonneg y hg.ne'
  by_contra hnot
  have hgap : y - x + 1 ≤ y / g - x / g := by omega
  have hmul := mul_le_mul_of_nonneg_left hgap hg.le
  have hnonneg := mul_nonneg (show 0 ≤ g - 1 by omega) (sub_nonneg.mpr hxy)
  nlinarith

def latticeInterval (u g left right : ℤ) : Finset ℤ :=
  Finset.Icc ((left - u) / g) ((right - u) / g)

def latticeCoordinates (u g : ℤ) (A : Finset ℤ) : Finset ℤ :=
  A.image (fun x => (x - u) / g)

theorem lattice_coordinate_reconstruct {u g x : ℤ} (hx : g ∣ x - u) :
    u + g * ((x - u) / g) = x := by
  rw [Int.mul_ediv_cancel' hx]
  ring

theorem latticeCoordinates_card (u g : ℤ) (A : Finset ℤ)
    (hclass : ∀ x ∈ A, g ∣ x - u) : (latticeCoordinates u g A).card = A.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy heq
  have h := congrArg (fun z : ℤ => u + g * z) heq
  simpa only [lattice_coordinate_reconstruct (hclass x hx),
    lattice_coordinate_reconstruct (hclass y hy)] using h

theorem latticeCoordinates_member {u g : ℤ} {A : Finset ℤ}
    (hclass : ∀ x ∈ A, g ∣ x - u) {y : ℤ} (hy : y ∈ latticeCoordinates u g A) :
    u + g * y ∈ A := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  simpa only [lattice_coordinate_reconstruct (hclass x hx)] using hx

theorem latticeCoordinates_subset_interval {u g left : ℤ} {M : ℕ} {A : Finset ℤ}
    (hg : 0 < g) (hA : A ⊆ Finset.Ico left (left + M)) :
    latticeCoordinates u g A ⊆ latticeInterval u g left (left + M - 1) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hleft, hright⟩ := Finset.mem_Ico.mp (hA hx)
  exact Finset.mem_Icc.mpr ⟨Int.ediv_le_ediv hg (by omega),
    Int.ediv_le_ediv hg (by omega)⟩

theorem latticeInterval_mono {u g a b p q : ℤ} (hg : 0 < g) (hp : a ≤ p) (hq : q ≤ b) :
    latticeInterval u g p q ⊆ latticeInterval u g a b := by
  intro x hx
  obtain ⟨hleft, hright⟩ := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨(Int.ediv_le_ediv hg (by omega)).trans hleft,
    hright.trans (Int.ediv_le_ediv hg (by omega))⟩

theorem latticeInterval_card_le {u g left : ℤ} {M : ℕ} (hg : 0 < g) (hM : 0 < M) :
    (latticeInterval u g left (left + M - 1)).card ≤ M := by
  have hwidth := ediv_interval_width (x := left - u) (y := left + M - 1 - u) hg (by omega)
  unfold latticeInterval
  rw [Int.card_Icc]
  omega

theorem latticeInterval_nonempty {u g p q : ℤ} (hg : 0 < g) (hpq : p ≤ q) :
    (latticeInterval u g p q).Nonempty := by
  exact ⟨(p - u) / g, Finset.mem_Icc.mpr ⟨le_rfl, Int.ediv_le_ediv hg (by omega)⟩⟩

theorem intervalCovered_Icc (a b : ℤ) :
    IntervalCovered (Finset.Icc a b).card (Finset.Icc a b) := by
  intro x hx
  obtain ⟨hax, hxb⟩ := Finset.mem_Icc.mp hx
  refine ⟨a, b, hax, hxb, ?_, Finset.Subset.refl _⟩
  rw [Int.card_Icc]
  omega

theorem lattice_core_card_lower {η : ℝ} {M : ℕ} {u p q : ℤ} {g : ℕ}
    (hη : 0 < η) (hg : 0 < g) (hpq : p ≤ q)
    (hp : (g : ℤ) ∣ p - u) (hq : (g : ℤ) ∣ q - u)
    (hgbound : η * g ≤ 2) (hspan : η ^ 3 * M / 32 ≤ ((q - p : ℤ) : ℝ)) :
    η ^ 4 * M / 64 ≤ ((latticeInterval u g p q).card : ℝ) := by
  have hgint : (0 : ℤ) < g := by exact_mod_cast hg
  have hab : (p - u) / (g : ℤ) ≤ (q - u) / (g : ℤ) := Int.ediv_le_ediv hgint (by omega)
  have hcard : ((latticeInterval u g p q).card : ℤ) =
      (q - u) / (g : ℤ) - (p - u) / (g : ℤ) + 1 := by
    unfold latticeInterval
    rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
    omega
  have hpointP := lattice_coordinate_reconstruct hp
  have hpointQ := lattice_coordinate_reconstruct hq
  have hidentity : (g : ℤ) * (latticeInterval u g p q).card = q - p + g := by
    rw [hcard]
    nlinarith
  have hreal : (g : ℝ) * ((latticeInterval u g p q).card : ℝ) =
      ((q - p : ℤ) : ℝ) + g := by exact_mod_cast hidentity
  have hupper : ((q - p : ℤ) : ℝ) ≤
      (g : ℝ) * ((latticeInterval u g p q).card : ℝ) := by
    have hgReal : (0 : ℝ) ≤ g := by positivity
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hupper hη.le
  have hgboundScaled := mul_le_mul_of_nonneg_right hgbound
    (by positivity : (0 : ℝ) ≤ (latticeInterval u g p q).card)
  have hspanScaled := mul_le_mul_of_nonneg_left hspan hη.le
  nlinarith

theorem lattice_core_means {S : ℕ → Finset ℤ} {cut u p q : ℤ} {j g : ℕ}
    (hg : 0 < g) (hp : (g : ℤ) ∣ p - u) (hq : (g : ℤ) ∣ q - u)
    (hcore : ∀ x : ℤ, p ≤ x → x ≤ q → (g : ℤ) ∣ x - u → DyadicMean S cut j x) :
    ∀ y ∈ latticeInterval u g p q, DyadicMean S cut j (u + g * y) := by
  intro y hy
  obtain ⟨hleft, hright⟩ := Finset.mem_Icc.mp hy
  have hg0 : (0 : ℤ) ≤ g := by omega
  have hleftMul := mul_le_mul_of_nonneg_left hleft hg0
  have hrightMul := mul_le_mul_of_nonneg_left hright hg0
  have hpointP := lattice_coordinate_reconstruct hp
  have hpointQ := lattice_coordinate_reconstruct hq
  apply hcore _ (by linarith) (by linarith)
  convert dvd_mul_right (g : ℤ) y using 1 <;> ring

end Erdos790.Upper
