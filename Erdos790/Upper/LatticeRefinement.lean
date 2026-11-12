import Erdos790.Upper.DyadicCombinations
import Erdos790.Upper.LatticeSums
import Erdos790.Upper.LatticeIntervals

/-!
# Refining a lattice of mixed means

An off-lattice selected point permits the old mixed means to fill a denser
lattice. The endpoint inequalities state the room required for the bounded
number of new selected-point copies.
-/

namespace Erdos790.Upper

theorem gcd_refinement_bounds {g d : ℤ} (hg : 0 < g) (hoff : ¬ g ∣ d) :
    0 < (Int.gcd g d : ℤ) ∧ 2 * (Int.gcd g d : ℤ) ≤ g := by
  have hpos : 0 < (Int.gcd g d : ℤ) := by
    exact_mod_cast Int.gcd_pos_of_ne_zero_left d (ne_of_gt hg)
  have hle := Int.gcd_le_left d hg
  have hne : (Int.gcd g d : ℤ) ≠ g := by
    intro heq
    exact hoff ((Int.gcd_eq_left_iff_dvd hg.le).mp heq)
  have hlt : (Int.gcd g d : ℤ) < g := lt_of_le_of_ne hle hne
  obtain ⟨k, hk⟩ := Int.gcd_dvd_left g d
  have htwo : 2 ≤ k := by nlinarith
  exact ⟨hpos, by nlinarith⟩

theorem DyadicMean.refine_lattice {S : ℕ → Finset ℤ}
    {cut u p q b t : ℤ} {j s g : ℕ}
    (hg : 0 < g) (hs : 0 < s) (hcapacity : g ≤ 2 ^ s)
    (hpq : p ≤ q) (hp : (g : ℤ) ∣ p - u) (hq : (g : ℤ) ∣ q - u)
    (hcore : ∀ x : ℤ, p ≤ x → x ≤ q → (g : ℤ) ∣ x - u →
      DyadicMean S cut j x)
    (hb : b ∈ S j)
    (hclass : (Int.gcd (g : ℤ) (b - u) : ℤ) ∣ t - u)
    (hlower : (2 : ℤ) ^ s * p + g * |b - p| ≤ (2 : ℤ) ^ s * t)
    (hupper : (2 : ℤ) ^ s * t ≤ (2 : ℤ) ^ s * q - g * |b - q|) :
    DyadicMean S cut (j + s) t := by
  have hgint : (0 : ℤ) < g := by exact_mod_cast hg
  obtain ⟨v, hvg, hres⟩ := bounded_gcd_residue hgint
    (dvd_mul_of_dvd_right hclass ((2 : ℤ) ^ s))
  have hvgnat : v < g := by exact_mod_cast hvg
  have hvpow : v < 2 ^ s := hvgnat.trans_le hcapacity
  let count := 2 ^ s - v
  have hcount : count + v = 2 ^ s := Nat.sub_add_cancel hvpow.le
  have hcountpos : 0 < count := by dsimp [count]; omega
  have hcastcount : (count : ℤ) + v = (2 : ℤ) ^ s := by exact_mod_cast hcount
  let N : ℤ := (2 : ℤ) ^ s * t - v * b
  have hendpoint : (g : ℤ) ∣ q - p := by
    convert dvd_sub hq hp using 1 <;> ring
  have hNdiv : (g : ℤ) ∣ N - count * p := by
    have hid : N - count * p =
        ((2 : ℤ) ^ s * (t - u) - v * (b - u)) - count * (p - u) := by
      dsimp [N]
      rw [← hcastcount]
      ring
    rw [hid]
    exact dvd_sub hres (dvd_mul_of_dvd_right hp (count : ℤ))
  have hvnonneg : (0 : ℤ) ≤ v := Int.natCast_nonneg v
  have hleftloss : (v : ℤ) * (b - p) ≤ g * |b - p| := by
    calc
      (v : ℤ) * (b - p) ≤ v * |b - p| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hvnonneg
      _ ≤ g * |b - p| := mul_le_mul_of_nonneg_right hvg.le (abs_nonneg _)
  have hrightloss : -((v : ℤ) * (b - q)) ≤ g * |b - q| := by
    calc
      -((v : ℤ) * (b - q)) = v * (-(b - q)) := by ring
      _ ≤ v * |b - q| := mul_le_mul_of_nonneg_left (neg_le_abs _) hvnonneg
      _ ≤ g * |b - q| := mul_le_mul_of_nonneg_right hvg.le (abs_nonneg _)
  have hcastp : (count : ℤ) * p = (2 : ℤ) ^ s * p - v * p := by
    rw [← hcastcount]
    ring
  have hcastq : (count : ℤ) * q = (2 : ℤ) ^ s * q - v * q := by
    rw [← hcastcount]
    ring
  have hNlower : (count : ℤ) * p ≤ N := by
    rw [hcastp]
    dsimp [N]
    nlinarith
  have hNupper : N ≤ (count : ℤ) * q := by
    rw [hcastq]
    dsimp [N]
    nlinarith
  obtain ⟨L, hlength, hL, hsum⟩ :=
    exact_length_lattice_sum hgint hpq hendpoint hNdiv hNlower hNupper
  have hne : L ≠ [] := by
    intro hempty
    rw [hempty, List.length_nil] at hlength
    omega
  apply DyadicMean.combine (v := v) (b := b) (L := L) hs hne ?_ (fun _ => hb) ?_ ?_
  · intro x hx
    obtain ⟨hpx, hxq, hxp⟩ := hL x hx
    apply hcore x hpx hxq
    convert dvd_add hxp hp using 1 <;> ring
  · rw [hlength]
    exact hcount
  · rw [hsum]
    dsimp [N]
    ring

theorem refined_dyadic_core {S : ℕ → Finset ℤ}
    {cut u p q b M : ℤ} {j s g : ℕ}
    (hg : 0 < g) (hs : 0 < s) (hcapacity : g ≤ 2 ^ s)
    (hp : (g : ℤ) ∣ p - u) (hq : (g : ℤ) ∣ q - u)
    (hcore : ∀ x : ℤ, p ≤ x → x ≤ q → (g : ℤ) ∣ x - u →
      DyadicMean S cut j x)
    (hb : b ∈ S j) (hoff : ¬ (g : ℤ) ∣ b - u)
    (hroom : 8 * (g : ℤ) + 8 ≤ q - p)
    (hbp : |b - p| ≤ 2 * M) (hbq : |b - q| ≤ 2 * M)
    (hscale : 8 * (g : ℤ) * M ≤ (2 : ℤ) ^ s * (q - p)) :
    let g' : ℕ := Int.gcd (g : ℤ) (b - u)
    0 < g' ∧ 2 * g' ≤ g ∧
      ∃ p' q' : ℤ, (g' : ℤ) ∣ p' - u ∧ (g' : ℤ) ∣ q' - u ∧
        p ≤ p' ∧ q' ≤ q ∧ q - p ≤ 4 * (q' - p') ∧
        ∀ x : ℤ, p' ≤ x → x ≤ q' → (g' : ℤ) ∣ x - u →
          DyadicMean S cut (j + s) x := by
  dsimp only
  have hgint : (0 : ℤ) < g := by exact_mod_cast hg
  obtain ⟨hnewpos, hnewbound⟩ := gcd_refinement_bounds hgint hoff
  have hnewroom : 8 * (Int.gcd (g : ℤ) (b - u) : ℤ) + 8 ≤ q - p := by omega
  obtain ⟨p', q', hpclass, hqclass, hpp, hqq, hpleft, hqright, hspan⟩ :=
    central_lattice_interval (u := u) hnewpos hnewroom
  refine ⟨by exact_mod_cast hnewpos, by exact_mod_cast hnewbound,
    p', q', hpclass, hqclass, hpp, hqq, hspan, ?_⟩
  intro x hpx hxq hxclass
  have hleft : q - p ≤ 4 * (x - p) := by omega
  have hright : q - p ≤ 4 * (q - x) := by omega
  have hpow : (0 : ℤ) ≤ (2 : ℤ) ^ s := pow_nonneg (by omega) _
  have hleftmul := mul_le_mul_of_nonneg_left hleft hpow
  have hrightmul := mul_le_mul_of_nonneg_left hright hpow
  have hleftloss := mul_le_mul_of_nonneg_left hbp hgint.le
  have hrightloss := mul_le_mul_of_nonneg_left hbq hgint.le
  apply DyadicMean.refine_lattice hg hs hcapacity (by omega) hp hq hcore hb hxclass
  · nlinarith
  · nlinarith

end Erdos790.Upper
