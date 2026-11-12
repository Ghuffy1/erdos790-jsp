import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Counting short arcs in finite cyclic groups
-/

open Finset

namespace Erdos790.Upper

def nearZeroResidues (p r : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter (fun a => min a.val (p - a.val) < r)

theorem nearZeroResidues_card_le (p r : ℕ) [NeZero p] :
    (nearZeroResidues p r).card ≤ 2 * r := by
  let left := (Finset.range r).image (fun a : ℕ => (a : ZMod p))
  let right := (Finset.range r).image (fun a : ℕ => -(a : ZMod p))
  have hsubset : nearZeroResidues p r ⊆ left ∪ right := by
    intro a ha
    have hsmall := (Finset.mem_filter.mp ha).2
    rcases min_lt_iff.mp hsmall with hl | hr
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨a.val, Finset.mem_range.mpr hl, by simp⟩
    · apply Finset.mem_union.mpr
      right
      refine Finset.mem_image.mpr ⟨p - a.val, Finset.mem_range.mpr hr, ?_⟩
      simp [Nat.cast_sub (ZMod.val_lt a).le]
  calc
    (nearZeroResidues p r).card ≤ (left ∪ right).card := Finset.card_le_card hsubset
    _ ≤ left.card + right.card := Finset.card_union_le _ _
    _ ≤ r + r := Nat.add_le_add
      ((Finset.card_image_le).trans_eq (Finset.card_range r))
      ((Finset.card_image_le).trans_eq (Finset.card_range r))
    _ = 2 * r := by omega

def residuePrefix (N p : ℕ) [NeZero p] (f : ZMod p → ZMod p)
    (bad : Finset (ZMod p)) : Finset ℕ :=
  (Finset.range N).filter (fun n => f (n : ZMod p) ∈ bad)

theorem residuePrefix_card_le {N p : ℕ} [NeZero p] (f : ZMod p → ZMod p)
    (hf : Function.Injective f) (bad : Finset (ZMod p)) :
    (residuePrefix N p f bad).card ≤ (N / p + 1) * bad.card := by
  let code := fun n : ℕ => (n / p, f (n : ZMod p))
  have hinj : Function.Injective code := by
    intro a b hab
    have hquot : a / p = b / p := congrArg Prod.fst hab
    have hresidue : (a : ZMod p) = (b : ZMod p) := hf (congrArg Prod.snd hab)
    have hmod : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).mp hresidue
    have ha := Nat.mod_add_div a p
    have hb := Nat.mod_add_div b p
    rw [hquot, hmod] at ha
    omega
  have hsubset : (residuePrefix N p f bad).image code ⊆
      (Finset.range (N / p + 1)) ×ˢ bad := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hn, hbad⟩ := Finset.mem_filter.mp hn
    have hdiv : n / p ≤ N / p := Nat.div_le_div_right (Finset.mem_range.mp hn).le
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by change n / p < N / p + 1; omega), hbad⟩
  calc
    (residuePrefix N p f bad).card = ((residuePrefix N p f bad).image code).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((Finset.range (N / p + 1)) ×ˢ bad).card := Finset.card_le_card hsubset
    _ = (N / p + 1) * bad.card := by simp

theorem nearZero_prefix_card_le {N p r : ℕ} [NeZero p]
    (f : ZMod p → ZMod p) (hf : Function.Injective f) :
    (residuePrefix N p f (nearZeroResidues p r)).card ≤ (N / p + 1) * (2 * r) :=
  (residuePrefix_card_le f hf _).trans
    (Nat.mul_le_mul_left _ (nearZeroResidues_card_le p r))

theorem nearZero_prefix_scaled_card_le {N p p0 : ℕ} [NeZero p]
    (hp : p0 ≤ p) (f : ZMod p → ZMod p) (hf : Function.Injective f) :
    (residuePrefix N p f (nearZeroResidues p (p / p0 + 1))).card * p0 ≤ 4 * (N + p) := by
  have hr : (p / p0 + 1) * p0 ≤ 2 * p := by
    have hdiv := Nat.div_mul_le_self p p0
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hN : (N / p + 1) * p ≤ N + p := by
    have hdiv := Nat.div_mul_le_self N p
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    _ ≤ ((N / p + 1) * (2 * (p / p0 + 1))) * p0 :=
      Nat.mul_le_mul_right p0 (nearZero_prefix_card_le f hf)
    _ = (2 * (N / p + 1)) * ((p / p0 + 1) * p0) := by ring
    _ ≤ (2 * (N / p + 1)) * (2 * p) := Nat.mul_le_mul_left _ hr
    _ = 4 * ((N / p + 1) * p) := by ring
    _ ≤ 4 * (N + p) := Nat.mul_le_mul_left 4 hN

theorem nearZero_prefix_window_bound {N p p0 : ℕ} [NeZero p]
    (hp : p0 ≤ p) (hwindow : p ≤ 8 * N)
    (f : ZMod p → ZMod p) (hf : Function.Injective f) :
    (residuePrefix N p f (nearZeroResidues p (p / p0 + 1))).card * p0 ≤ 36 * N := by
  have h := nearZero_prefix_scaled_card_le (N := N) hp f hf
  omega

theorem conditioned_bad_count_bound {bad total N v L : ℕ}
    (hv : 0 < v) (hbad : bad * v ^ 2 ≤ 36 * N)
    (hdensity : N ≤ 4 * v * total) (hscale : 14400 * L ≤ v) :
    100 * L * bad ≤ total := by
  have hscaled : v * (bad * v) ≤ v * (144 * total) := by
    calc
      v * (bad * v) = bad * v ^ 2 := by ring
      _ ≤ 36 * N := hbad
      _ ≤ 36 * (4 * v * total) := Nat.mul_le_mul_left 36 hdensity
      _ = v * (144 * total) := by ring
  have hcancel : bad * v ≤ 144 * total := Nat.le_of_mul_le_mul_left hscaled hv
  have hsmall : 144 * (100 * L * bad) ≤ 144 * total := by
    calc
      144 * (100 * L * bad) = bad * (14400 * L) := by ring
      _ ≤ bad * v := Nat.mul_le_mul_left bad hscale
      _ ≤ 144 * total := hcancel
  exact Nat.le_of_mul_le_mul_left hsmall (by decide)

end Erdos790.Upper
