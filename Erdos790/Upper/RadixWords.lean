import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Finite radix encodings for the deterministic offsets
-/

namespace Erdos790.Upper

def radixValue {d : ℕ} (q : ℕ) (digits : Fin d → ℕ) : ℕ :=
  ∑ i, digits i * q ^ i.val

theorem ofDigits_ofFn_eq_radixValue {d : ℕ} (q : ℕ) (digits : Fin d → ℕ) :
    Nat.ofDigits q (List.ofFn digits) = radixValue q digits := by
  induction d with
  | zero => simp [radixValue]
  | succ d ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, ih]
    simp only [radixValue, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
      Fin.val_succ, pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem radixValue_lt_pow {d q : ℕ} (hq : 1 < q) (digits : Fin d → ℕ)
    (hdigits : ∀ i, digits i < q) : radixValue q digits < q ^ d := by
  have hbound : ∀ a ∈ List.ofFn digits, a < q := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hdigits i
  simpa only [List.length_ofFn, ofDigits_ofFn_eq_radixValue] using
    Nat.ofDigits_lt_base_pow_length hq hbound

theorem radixValue_injective {d q : ℕ} (hq : 1 < q) :
    Function.Injective (fun digits : Fin d → Fin q => radixValue q (fun i => (digits i).val)) := by
  intro a b hab
  have hlist : List.ofFn (fun i => (a i).val) = List.ofFn (fun i => (b i).val) :=
    Nat.ofDigits_inj_of_len_eq hq (by simp)
      (by intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact (a i).isLt)
      (by intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact (b i).isLt)
      (by simpa only [ofDigits_ofFn_eq_radixValue] using hab)
  have hfun := List.ofFn_injective hlist
  funext i
  exact Fin.ext (congrFun hfun i)

theorem radixValue_add {d : ℕ} (q : ℕ) (a b : Fin d → ℕ) :
    radixValue q (fun i => a i + b i) = radixValue q a + radixValue q b := by
  simp only [radixValue, add_mul, Finset.sum_add_distrib]

theorem radixValue_eq_of_bounded_digits {d q : ℕ} (hq : 1 < q)
    (a b : Fin d → ℕ) (ha : ∀ i, a i < q) (hb : ∀ i, b i < q)
    (h : radixValue q a = radixValue q b) : a = b := by
  let a' := fun i => (⟨a i, ha i⟩ : Fin q)
  let b' := fun i => (⟨b i, hb i⟩ : Fin q)
  have hab : a' = b' := radixValue_injective hq h
  funext i
  exact congrArg Fin.val (congrFun hab i)

theorem radixValue_ones_bound {q : ℕ} (hq : 2 ≤ q) (d : ℕ) :
    radixValue q (fun _ : Fin d => 1) < 2 * q ^ (d - 1) := by
  induction d with
  | zero => simp [radixValue]
  | succ d ih =>
    cases d with
    | zero => simp [radixValue]
    | succ n =>
      have hstep : radixValue q (fun _ : Fin (n + 1 + 1) => 1) =
          radixValue q (fun _ : Fin (n + 1) => 1) + q ^ (n + 1) := by
        simp only [radixValue, Fin.sum_univ_castSucc, one_mul, Fin.val_castSucc,
          Fin.val_last]
      simp only [Nat.add_sub_cancel] at ih ⊢
      rw [hstep, pow_succ]
      have hpow : 0 < q ^ n := Nat.pow_pos (by omega)
      nlinarith

theorem radixValue_lt_scaled_power {d q D : ℕ} (hq : 2 ≤ q) (hD : 0 < D)
    (digits : Fin d → ℕ) (hbound : ∀ i, digits i ≤ D) :
    radixValue q digits < 2 * D * q ^ (d - 1) := by
  have hle : radixValue q digits ≤ D * radixValue q (fun _ : Fin d => 1) := by
    unfold radixValue
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa using Nat.mul_le_mul_right (q ^ i.val) (hbound i)
  calc
    radixValue q digits ≤ D * radixValue q (fun _ : Fin d => 1) := hle
    _ < D * (2 * q ^ (d - 1)) := Nat.mul_lt_mul_of_pos_left (radixValue_ones_bound hq d) hD
    _ = 2 * D * q ^ (d - 1) := by ring

end Erdos790.Upper
