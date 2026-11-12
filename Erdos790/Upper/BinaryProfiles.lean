import Erdos790.Upper.BinaryRadixGap
import Erdos790.Upper.MixedMeanResidual
import Mathlib.Data.Nat.Dist

/-!
# The highest differing bit gives a definite radix separation
-/

namespace Erdos790.Upper

theorem nat_dist_cast_int (u v : ℕ) : (Nat.dist u v : ℤ) = |(u : ℤ) - v| := by
  rcases le_total u v with huv | hvu
  · have hcast : (u : ℤ) ≤ v := by exact_mod_cast huv
    rw [Nat.dist_eq_sub_of_le huv, Nat.cast_sub huv, abs_of_nonpos (sub_nonpos.mpr hcast)]
    ring
  · have hcast : (v : ℤ) ≤ u := by exact_mod_cast hvu
    rw [Nat.dist_eq_sub_of_le_right hvu, Nat.cast_sub hvu, abs_of_nonneg (sub_nonneg.mpr hcast)]

theorem nativeTentValue_bit_difference {d : ℕ} (amplification q constant scale step t : ℕ)
    (a b : Fin d → Fin 2) :
    (nativeTentValue amplification q constant scale step t a : ℤ) -
        (nativeTentValue amplification q constant scale step t b : ℤ) =
      (scale : ℤ) * ((radixValue q (fun h => (a h).val) : ℤ) -
        (radixValue q (fun h => (b h).val) : ℤ)) := by
  unfold nativeTentValue
  rw [radixValue_add, radixValue_add]
  push_cast
  ring

theorem nativeTentValue_bit_dist {d : ℕ} (amplification q constant scale step t : ℕ)
    (a b : Fin d → Fin 2) :
    Nat.dist (nativeTentValue amplification q constant scale step t a)
        (nativeTentValue amplification q constant scale step t b) =
      scale * Nat.dist (radixValue q (fun h => (a h).val))
        (radixValue q (fun h => (b h).val)) := by
  apply Int.natCast_inj.mp
  rw [nat_dist_cast_int, nativeTentValue_bit_difference, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℤ) ≤ scale), Nat.cast_mul, nat_dist_cast_int]

theorem binary_profile_gap {d q : ℕ} (hq : 3 ≤ q) (a b : Fin d → Fin 2)
    (allowed : Finset (Fin d)) (hneq : a ≠ b)
    (hfixed : ∀ h, h ∉ allowed → a h = b h) :
    ∃ H ∈ allowed, a H ≠ b H ∧ (∀ h : Fin d, H < h → a h = b h) ∧
      (q : ℤ) ^ H.val ≤ 2 * |(radixValue q (fun h => (a h).val) : ℤ) -
        (radixValue q (fun h => (b h).val) : ℤ)| ∧
      |(radixValue q (fun h => (a h).val) : ℤ) -
        (radixValue q (fun h => (b h).val) : ℤ)| < 2 * (q : ℤ) ^ H.val := by
  classical
  let differing := Finset.univ.filter (fun h : Fin d => a h ≠ b h)
  have hnonempty : differing.Nonempty := by
    obtain ⟨h, hh⟩ : ∃ h, a h ≠ b h := by
      by_contra h
      push_neg at h
      exact hneq (funext h)
    exact ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
  let H := differing.max' hnonempty
  have hHdiffering : H ∈ differing := Finset.max'_mem _ _
  have hHneq : a H ≠ b H := (Finset.mem_filter.mp hHdiffering).2
  have hHallowed : H ∈ allowed := by
    by_contra hnot
    exact hHneq (hfixed H hnot)
  have hhigh : ∀ h : Fin d, H < h → a h = b h := by
    intro h hh
    by_contra hne
    have hmem : h ∈ differing := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    have hle : h ≤ H := Finset.le_max' differing h hmem
    exact (not_le_of_gt hh) hle
  let digit := fun h : Fin d => ((a h).val : ℤ) - (b h).val
  let difference : ℤ := (radixValue q (fun h => (a h).val) : ℤ) -
    (radixValue q (fun h => (b h).val) : ℤ)
  have hsum : (∑ h : Fin d, digit h * (q : ℤ) ^ h.val) = difference := by
    dsimp [difference, radixValue]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h _
    dsimp [digit]
    ring
  have hbound : ∀ h : Fin d, |digit h| ≤ 1 := by
    intro h
    have ha := (a h).isLt
    have hb := (b h).isLt
    dsimp [digit]
    rw [abs_le]
    constructor <;> omega
  have hzero : ∀ h : Fin d, H < h → digit h = 0 := by
    intro h hh
    dsimp [digit]
    rw [hhigh h hh, sub_self]
  have hleading : digit H = 1 ∨ digit H = -1 := by
    have ha := (a H).isLt
    have hb := (b H).isLt
    have hvals : (a H).val ≠ (b H).val := fun h => hHneq (Fin.ext h)
    dsimp [digit]
    omega
  refine ⟨H, hHallowed, hHneq, hhigh, ?_⟩
  change (q : ℤ) ^ H.val ≤ 2 * |difference| ∧
    |difference| < 2 * (q : ℤ) ^ H.val
  have hqInt : (3 : ℤ) ≤ q := by exact_mod_cast hq
  have hpower : 0 < (q : ℤ) ^ H.val := by positivity
  rcases hleading with hpos | hneg
  · have h := finite_binary_radix_gap digit H hqInt hpos (fun h _ => hbound h) hzero
    rw [hsum] at h
    have hnonneg : 0 ≤ difference := by nlinarith [h.1]
    simpa only [abs_of_nonneg hnonneg] using h
  · have h := finite_binary_radix_gap (fun h => -digit h) H hqInt
      (by rw [hneg]; norm_num) (fun h _ => by simpa only [abs_neg] using hbound h)
      (fun h hh => by rw [hzero h hh, neg_zero])
    have hnegSum : (∑ h : Fin d, -digit h * (q : ℤ) ^ h.val) = -difference := by
      rw [← hsum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro h _
      ring
    rw [hnegSum] at h
    have hnonpos : difference ≤ 0 := by nlinarith [h.1]
    simpa only [abs_of_nonpos hnonpos] using h

theorem binary_profile_dist {d q : ℕ} (hq : 3 ≤ q) (a b : Fin d → Fin 2)
    (allowed : Finset (Fin d)) (hneq : a ≠ b)
    (hfixed : ∀ h, h ∉ allowed → a h = b h) :
    ∃ H ∈ allowed, q ^ H.val ≤
        2 * Nat.dist (radixValue q (fun h => (a h).val)) (radixValue q (fun h => (b h).val)) ∧
      Nat.dist (radixValue q (fun h => (a h).val)) (radixValue q (fun h => (b h).val)) <
        2 * q ^ H.val := by
  obtain ⟨H, hH, _, _, hlower, hupper⟩ := binary_profile_gap hq a b allowed hneq hfixed
  refine ⟨H, hH, ?_, ?_⟩
  · rw [← nat_dist_cast_int] at hlower
    exact_mod_cast hlower
  · rw [← nat_dist_cast_int] at hupper
    exact_mod_cast hupper

end Erdos790.Upper
