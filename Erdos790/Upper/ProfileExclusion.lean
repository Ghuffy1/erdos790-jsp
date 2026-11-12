import Erdos790.Upper.BinaryProfiles
import Erdos790.Upper.ResidualRelations

/-!
# Uniqueness of the allowed bit profile at a fixed level and coordinate
-/

namespace Erdos790.Upper

theorem selected_profile_unique {d q Q X j K threshold amplification constant step t : ℕ}
    (C B : Finset ℕ) (allowed : Finset (Fin d)) (a b : Fin d → Fin 2)
    (hq : 3 ≤ q) (hX : 0 < X)
    (hC : ∀ x ∈ C, X ≤ x ∧ x < 2 * X)
    (hcover : SumCover C K threshold) (hB : RepeatedSumFree (q ^ 6) B)
    (hthreshold : 2 * threshold ≤ q ^ 2 * X)
    (hdata : ∀ H ∈ allowed, ∃ i, i ≤ j ∧ K ≤ (levelSlice i C B).card ∧
      q ^ 2 * X ≤ Q * 2 ^ (j - i) * q ^ H.val ∧
      Q * 2 ^ (j - i) * q ^ H.val ≤ q ^ 4 * X)
    (hfixed : ∀ h, h ∉ allowed → a h = b h)
    (ha : 2 ^ j * nativeTentValue amplification q constant Q step t a ∈ B)
    (hb : 2 ^ j * nativeTentValue amplification q constant Q step t b ∈ B) : a = b := by
  classical
  by_contra hneq
  obtain ⟨H, hH, hlower, hupper⟩ := binary_profile_dist hq a b allowed hneq hfixed
  obtain ⟨i, hij, hheavy, hscaleLower, hscaleUpper⟩ := hdata H hH
  let D := Nat.dist (radixValue q (fun h => (a h).val))
    (radixValue q (fun h => (b h).val))
  let N := 2 ^ (j - i) * Nat.dist
    (nativeTentValue amplification q constant Q step t a)
    (nativeTentValue amplification q constant Q step t b)
  have hN : N = Q * 2 ^ (j - i) * D := by
    dsimp [N, D]
    rw [nativeTentValue_bit_dist]
    ring
  have hlowerN : q ^ 2 * X ≤ 2 * N := by
    calc
      q ^ 2 * X ≤ Q * 2 ^ (j - i) * q ^ H.val := hscaleLower
      _ ≤ Q * 2 ^ (j - i) * (2 * D) := Nat.mul_le_mul_left _ hlower
      _ = 2 * N := by rw [hN]; ring
  have hupperN : N ≤ q ^ 5 * X := by
    calc
      N = Q * 2 ^ (j - i) * D := hN
      _ ≤ Q * 2 ^ (j - i) * (2 * q ^ H.val) := Nat.mul_le_mul_left _ hupper.le
      _ = 2 * (Q * 2 ^ (j - i) * q ^ H.val) := by ring
      _ ≤ 2 * (q ^ 4 * X) := Nat.mul_le_mul_left _ hscaleUpper
      _ ≤ q * (q ^ 4 * X) := Nat.mul_le_mul_right _ (by omega)
      _ = q ^ 5 * X := by ring
  have hfour : 4 ≤ q ^ 2 := by nlinarith
  have htwoN : 2 * X ≤ N := by
    have h := (Nat.mul_le_mul_right X hfour).trans hlowerN
    omega
  have harity : 1 + q ^ 5 ≤ q ^ 6 := by
    have hone : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ (by omega)
    calc
      1 + q ^ 5 ≤ 2 * q ^ 5 := by omega
      _ ≤ q * q ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = q ^ 6 := by ring
  exact two_point_residual_impossible hX hC hcover hheavy hB ha hb hij
    (by change threshold ≤ N; omega) htwoN hupperN harity

end Erdos790.Upper
