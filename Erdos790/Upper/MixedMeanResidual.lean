import Erdos790.Upper.TentResidual
import Erdos790.Upper.DyadicRescaling
import Erdos790.Upper.ScaleArithmetic

/-!
# Actual dyadic means produce a bounded positive integer residual
-/

namespace Erdos790.Upper

def nativeTentValue {d : ℕ} (amplification q constant scale step t : ℕ)
    (bits : Fin d → Fin 2) : ℕ :=
  constant + scale * (t * step + radixValue q
    (fun h => amplification * periodicTent (2 ^ (d + h.val)) t + (bits h).val))

theorem nativeTentValue_coe {d : ℕ} (amplification q constant scale step t : ℕ)
    (bits : Fin d → Fin 2) :
    (nativeTentValue amplification q constant scale step t bits : ℤ) =
      encodedTentValue amplification q constant ((scale : ℤ) * step) scale t bits := by
  unfold nativeTentValue encodedTentValue radixValue tentDigit
  push_cast
  ring

theorem dyadic_mean_residual {d earlier start j delay width Q U C head a : ℕ}
    (amplification : ℕ) (H : Fin d) (S : ℕ → Finset ℤ)
    (word : ℕ → ℤ → Fin d → Fin 2) (B : Finset ℕ)
    (hwidth : 0 < width) (hQ : 0 < Q) (hbase : earlier ≤ start)
    (hamp : amplification = 2 ^ (delay + 3)) (hj : j < start + delay)
    (hD : (amplification : ℤ) * AuxiliaryParameters.timeCount d + 1 ≤ (2 : ℤ) ^ width - 1)
    (halign : 2 * 2 ^ (d + H.val) ∣ a)
    (hindexLower : d * width + 2 * width ≤ j - earlier + width * H.val)
    (hindexUpper : j - earlier + width * H.val < d * width + 4 * width)
    (hS : ∀ k, ∀ t ∈ S k, start ≤ k ∧ (a : ℤ) ≤ t ∧ t < (a : ℤ) + 2 * 2 ^ (d + H.val))
    (hword : ∀ k, ∀ t ∈ S k, ∀ h : Fin d, H < h → word k t h = word j head h)
    (hselected : ∀ k, ∀ t ∈ S k,
      2 ^ k * nativeTentValue amplification (2 ^ width) C Q U t.toNat (word k t) ∈ B)
    (hhead : (head : ℤ) ∈ S j)
    (hmean : DyadicMean S ((a : ℤ) + 2 ^ (d + H.val)) j head) :
    ∃ near : List ℕ, ∃ residual : ℕ,
      (∀ y ∈ near, y ∈ B) ∧ near.length ≤ 2 ^ delay ∧
      2 ^ j * nativeTentValue amplification (2 ^ width) C Q U head (word j head) =
        near.sum + 2 ^ earlier * residual ∧
      (2 ^ width) ^ 2 * (Q * (2 ^ width) ^ d) ≤ residual ∧
      residual ≤ (2 ^ width) ^ 5 * (Q * (2 ^ width) ^ d) := by
  classical
  have hstart : start ≤ j := (hS j head hhead).1
  obtain ⟨n, level, coordinate, hdata, hmass, hmoment, hleft, hright, hlength⟩ :=
    hmean.finite_rescaled_witness hbase hstart (fun k t ht => (hS k t ht).1)
  let q := 2 ^ width
  let weight := fun i : Fin n => (2 : ℤ) ^ (level i - earlier)
  let naturalCoordinate := fun i : Fin n => (coordinate i).toNat
  let bits := fun i : Fin n => word (level i) (coordinate i)
  let point := fun k t => nativeTentValue amplification q C Q U (Int.toNat t) (word k t)
  have hcoordinate0 : ∀ i : Fin n, 0 ≤ coordinate i := by
    intro i
    exact (Int.natCast_nonneg a).trans (hS _ _ (hdata i).2.2).2.1
  have hcoordinate : ∀ i : Fin n, (naturalCoordinate i : ℤ) = coordinate i :=
    fun i => Int.toNat_of_nonneg (hcoordinate0 i)
  have hcell : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      a ≤ naturalCoordinate i ∧ naturalCoordinate i < a + 2 * 2 ^ (d + H.val) := by
    intro i _
    have h := (hS _ _ (hdata i).2.2).2
    constructor
    · exact_mod_cast h.1.trans_eq (hcoordinate i).symm
    · have h' : (naturalCoordinate i : ℤ) < (a : ℤ) + 2 * 2 ^ (d + H.val) := by
        simpa only [hcoordinate] using h.2
      exact_mod_cast h'
  have hheadCell : a ≤ head ∧ head < a + 2 * 2 ^ (d + H.val) := by
    have h := (hS j head hhead).2
    exact_mod_cast h
  have hmoment' : (∑ i : Fin n, weight i * (naturalCoordinate i : ℤ)) =
      (2 : ℤ) ^ (j - earlier) * head := by
    simpa only [weight, hcoordinate] using hmoment
  have hminimum : ∀ i : Fin n, (2 : ℤ) ^ (start - earlier) ≤ weight i := by
    intro i
    dsimp [weight]
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.sub_le_sub_right (hdata i).1 earlier)
  have hleft' : ∃ i ∈ (Finset.univ : Finset (Fin n)),
      naturalCoordinate i < a + 2 ^ (d + H.val) ∧ (2 : ℤ) ^ (start - earlier) ≤ weight i := by
    obtain ⟨i, hi⟩ := hleft
    refine ⟨i, Finset.mem_univ _, ?_, hminimum i⟩
    have h' : (naturalCoordinate i : ℤ) < (a : ℤ) + 2 ^ (d + H.val) := by rwa [hcoordinate]
    exact_mod_cast h'
  have hright' : ∃ i ∈ (Finset.univ : Finset (Fin n)),
      a + 2 ^ (d + H.val) ≤ naturalCoordinate i ∧ (2 : ℤ) ^ (start - earlier) ≤ weight i := by
    obtain ⟨i, hi⟩ := hright
    refine ⟨i, Finset.mem_univ _, ?_, hminimum i⟩
    have h' : (a : ℤ) + 2 ^ (d + H.val) ≤ (naturalCoordinate i : ℤ) := by rwa [hcoordinate]
    exact_mod_cast h'
  have hq : 2 ≤ q := by
    dsimp [q]
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) hwidth
  have hscale : 2 * (2 : ℤ) ^ (j - earlier) ≤
      (amplification : ℤ) * (2 : ℤ) ^ (start - earlier) := by
    rw [hamp, Nat.cast_pow, Nat.cast_ofNat]
    exact_mod_cast dyadic_amplification_weight_bound hbase hstart hj
  have hgeometry := mixed_tent_residual_bounds Finset.univ weight naturalCoordinate bits head
    (word j head) amplification q a H
    (constant := (C : ℤ)) (step := (Q : ℤ) * U) (scale := (Q : ℤ))
    (by positivity) (by exact_mod_cast hQ) hq hD (fun i _ => by dsimp [weight]; positivity)
    halign hheadCell hcell (fun h hh i _ => hword _ _ (hdata i).2.2 h hh)
    hmass hmoment' hleft' hright' hscale
  let difference : ℤ := (2 : ℤ) ^ (j - earlier) * (point j head : ℤ) -
    ∑ i : Fin n, weight i * (point (level i) (coordinate i) : ℤ)
  have hgeometry' : (Q : ℤ) * (2 : ℤ) ^ (j - earlier) * (q : ℤ) ^ H.val ≤ difference ∧
      difference < (Q : ℤ) * (2 : ℤ) ^ (j - earlier) * (q : ℤ) ^ (H.val + 1) := by
    simpa only [difference, point, Int.toNat_natCast, nativeTentValue_coe,
      naturalCoordinate, bits] using hgeometry
  have hdifference0 : 0 ≤ difference := by
    have hpos : (0 : ℤ) < (Q : ℤ) * 2 ^ (j - earlier) * (q : ℤ) ^ H.val := by
      have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
      have hq' : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
      positivity
    exact hpos.le.trans hgeometry'.1
  let residual := difference.toNat
  have hresidual : (residual : ℤ) = difference := Int.toNat_of_nonneg hdifference0
  have hscaleBounds := assigned_residual_scale_bounds (Q := Q) hindexLower hindexUpper
  have hlowerInt : ((q ^ 2 * (Q * q ^ d) : ℕ) : ℤ) ≤ difference := by
    have h := hscaleBounds.1
    have h' : ((q ^ 2 * (Q * q ^ d) : ℕ) : ℤ) ≤
        (Q : ℤ) * (2 : ℤ) ^ (j - earlier) * (q : ℤ) ^ H.val := by exact_mod_cast h
    exact h'.trans hgeometry'.1
  have hupperInt : difference ≤ ((q ^ 5 * (Q * q ^ d) : ℕ) : ℤ) := by
    have h := hscaleBounds.2
    have h' : (Q : ℤ) * (2 : ℤ) ^ (j - earlier) * (q : ℤ) ^ (H.val + 1) ≤
        ((q ^ 5 * (Q * q ^ d) : ℕ) : ℤ) := by exact_mod_cast h
    exact hgeometry'.2.le.trans h'
  let near := List.ofFn (fun i : Fin n => 2 ^ level i * point (level i) (coordinate i))
  have hrelation := dyadic_residual_identity Finset.univ level
    (fun i => (point (level i) (coordinate i) : ℤ))
    (fun i _ => hbase.trans (hdata i).1) (hbase.trans hstart) hresidual
  have hnearSum : (near.sum : ℤ) = ∑ i : Fin n, (2 : ℤ) ^ level i * (point (level i) (coordinate i) : ℤ) := by
    dsimp [near]
    rw [Fin.sum_ofFn]
    push_cast
    rfl
  refine ⟨near, residual, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact hselected _ _ (hdata i).2.2
  · have hpower := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show j - start ≤ delay by omega)
    simpa only [near, List.length_ofFn] using hlength.trans hpower
  · rw [← hnearSum] at hrelation
    simpa only [point, Int.toNat_natCast] using (show
      2 ^ j * nativeTentValue amplification q C Q U head (word j head) = near.sum + 2 ^ earlier * residual by
        exact_mod_cast hrelation)
  · rw [← hresidual] at hlowerInt
    exact_mod_cast hlowerInt
  · rw [← hresidual] at hupperInt
    exact_mod_cast hupperInt

end Erdos790.Upper
