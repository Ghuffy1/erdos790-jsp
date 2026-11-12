import Erdos790.Upper.ClusterRefinement

/-!
# The lattice core carried between stable periods
-/

namespace Erdos790.Upper

structure MeanCoreData where
  modulus : ℕ
  lower : ℤ
  upper : ℤ

structure MeanCoreValid (A : ℕ → Finset ℤ) (cut u left : ℤ)
    (M initialModulus : ℕ) (initialSpan : ℝ) (time : ℕ) (core : MeanCoreData) : Prop where
  positive : 0 < core.modulus
  modulus_le : core.modulus ≤ initialModulus
  lower_class : (core.modulus : ℤ) ∣ core.lower - u
  upper_class : (core.modulus : ℤ) ∣ core.upper - u
  ordered : core.lower ≤ core.upper
  inside_left : left ≤ core.lower
  inside_right : core.upper < left + M
  span_invariant : initialSpan * (core.modulus : ℝ) ^ 2 ≤
    ((core.upper - core.lower : ℤ) : ℝ) * (initialModulus : ℝ) ^ 2
  means : ∀ x : ℤ, core.lower ≤ x → x ≤ core.upper →
    (core.modulus : ℤ) ∣ x - u → DyadicMean A cut time x

theorem DyadicMean.mono_time {A : ℕ → Finset ℤ} {cut x : ℤ} {a b : ℕ}
    (h : DyadicMean A cut a x) (hab : a ≤ b) : DyadicMean A cut b x := by
  have hsteps : ∀ n, DyadicMean A cut (a + n) x := by
    intro n
    induction n with
    | zero => simpa only [Nat.add_zero] using h
    | succ n ih => simpa only [Nat.add_assoc] using ih.carry
  simpa only [Nat.add_sub_of_le hab] using hsteps (b - a)

theorem MeanCoreValid.modulus_bound {A : ℕ → Finset ℤ} {cut u left : ℤ}
    {M initialModulus time s : ℕ} {initialSpan : ℝ} {core : MeanCoreData}
    (h : MeanCoreValid A cut u left M initialModulus initialSpan time core)
    (hbound : clusterDensity s * initialModulus ≤ 2) :
    clusterDensity s * core.modulus ≤ 2 :=
  (mul_le_mul_of_nonneg_left (by exact_mod_cast h.modulus_le) (clusterDensity_pos s).le).trans hbound

theorem MeanCoreValid.span_lower {A : ℕ → Finset ℤ} {cut u left : ℤ}
    {M initialModulus time s : ℕ} {initialSpan : ℝ} {core : MeanCoreData}
    (h : MeanCoreValid A cut u left M initialModulus initialSpan time core)
    (hbound : clusterDensity s * initialModulus ≤ 2)
    (hseed : clusterDensity s * M / 8 ≤ initialSpan) :
    clusterDensity s ^ 3 * M / 32 ≤ ((core.upper - core.lower : ℤ) : ℝ) := by
  apply refinement_span_lower (clusterDensity_pos s)
    (by exact_mod_cast (sub_nonneg.mpr h.ordered)) (by positivity) (by positivity)
    (by exact_mod_cast (show 1 ≤ core.modulus by have := h.positive; omega))
    hbound hseed h.span_invariant

theorem MeanCoreValid.refine {A : ℕ → Finset ℤ} {cut u left b : ℤ}
    {M initialModulus time j s d : ℕ} {initialSpan : ℝ} {core : MeanCoreData}
    (h : MeanCoreValid A cut u left M initialModulus initialSpan time core)
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hM : 2 ^ d ≤ M)
    (hbound : clusterDensity s * initialModulus ≤ 2)
    (hseed : clusterDensity s * M / 8 ≤ initialSpan)
    (htime : time ≤ j) (hb : b ∈ A j) (hbRange : b ∈ Finset.Ico left (left + M))
    (hoff : ¬ (core.modulus : ℤ) ∣ b - u) :
    ∃ next : MeanCoreData,
      MeanCoreValid A cut u left M initialModulus initialSpan (j + (s + 28)) next ∧
        2 * next.modulus ≤ core.modulus := by
  have hspan := h.span_lower hbound hseed
  have hmeans : ∀ x : ℤ, core.lower ≤ x → x ≤ core.upper →
      (core.modulus : ℤ) ∣ x - u → DyadicMean A cut j x :=
    fun x hxlo hxhi hxclass => (h.means x hxlo hxhi hxclass).mono_time htime
  have hinsideLeft := h.inside_left
  have hinsideRight := h.inside_right
  have hordered := h.ordered
  have hbp : |b - core.lower| ≤ 2 * (M : ℤ) := by
    have hbr := Finset.mem_Ico.mp hbRange
    rw [abs_le]
    constructor <;> omega
  have hbq : |b - core.upper| ≤ 2 * (M : ℤ) := by
    have hbr := Finset.mem_Ico.mp hbRange
    rw [abs_le]
    constructor <;> omega
  obtain ⟨hpositive, hhalve, p, q, hp, hq, hplower, hqupper, hquarter, hnewMeans⟩ :=
    cluster_refined_dyadic_core hd hs hM h.positive (h.modulus_bound hbound)
      h.lower_class h.upper_class hmeans hb hoff hspan hbp hbq
  let next : MeanCoreData := ⟨Int.gcd (core.modulus : ℤ) (b - u), p, q⟩
  have hDensity := clusterDensity_pos s
  have hinitNonneg : 0 ≤ initialSpan := (by positivity : 0 ≤ clusterDensity s * M / 8).trans hseed
  have hinvariant : initialSpan * (next.modulus : ℝ) ^ 2 ≤
      ((q - p : ℤ) : ℝ) * (initialModulus : ℝ) ^ 2 := by
    exact refinement_span_invariant hinitNonneg
      (show (0 : ℝ) ≤ (next.modulus : ℝ) by positivity)
      (by exact_mod_cast hhalve) (by exact_mod_cast hquarter) h.span_invariant
  refine ⟨next, ?_, hhalve⟩
  exact {
    positive := hpositive
    modulus_le := by
      change Int.gcd (core.modulus : ℤ) (b - u) ≤ initialModulus
      have := h.modulus_le
      omega
    lower_class := hp
    upper_class := hq
    ordered := by
      change p ≤ q
      omega
    inside_left := h.inside_left.trans hplower
    inside_right := hqupper.trans_lt h.inside_right
    span_invariant := hinvariant
    means := hnewMeans
  }

end Erdos790.Upper
