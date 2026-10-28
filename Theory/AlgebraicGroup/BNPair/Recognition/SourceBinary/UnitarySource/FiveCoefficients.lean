module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive

/-!
# Recovering the U₅ mixed coefficient from source group laws

Fong--Seitz II, (8.24)--(8.31), printed p.207, first leaves one Hermitian
coordinate unknown. Associativity supplies its two functional equations;
the actual Cartan action supplies its covariance. In the ordinary branch,
a nonfixed scalar, its conjugate and its trace force the norm coefficient.

Here the argument is performed directly on the A,D,C,B root maps in the
presentation convention. The B and D parameter groups remain nonabelian.
The unknown correction has only its first coordinate specified: its second
coordinate is proved, not a hypothesis. This avoids transplanting the book's
conjugated coefficient into a crossing rule with a different convention.

This does not construct these root maps or their preceding relations from
the original BN-pair. The required Cartan elements and the nonfixed scalar
are also still source obligations. The exceptional q=4 branch of (8C),
where this scalar is unavailable, requires the separate pp.209--210 argument.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FiveCoefficients
variable {E Y : Type*} [Field E] [CharP E 2] [Group Y]

/-- A polarized function with the three actual norm-scaling laws is the norm form. No finiteness or field-order restriction is used. -/
theorem norm_rigidity (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (f : E → E) (z θ : E) (hθ : θ + σ θ ≠ 0)
    (hadd : ∀ a b, f (a+b) = f a + f b + z*(a*σ b+b*σ a))
    (hscale : ∀ t ∈ ({θ,σ θ,θ+σ θ} : Set E), ∀ a,
      f (t*a) = t*σ t*f a) (a : E) : f a = a*σ a*z := by
  have h := hadd (θ*a) (σ θ*a)
  rw [← add_mul, hscale _ (by simp), hscale _ (by simp), hscale _ (by simp)] at h
  simp only [map_add, map_mul, hσ θ] at h
  have hsq : (θ+σ θ)^2 ≠ 0 := pow_ne_zero 2 hθ
  apply mul_left_cancel₀ hsq
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h

variable (J : HermitianForm 5 E)
variable (r : PositiveMaps Y (Multiplicative E) (FivePositive.Parameter J)
  (Multiplicative E) (FivePositive.Parameter J))
variable (T : FivePositive.Parameter J → E → FivePositive.Parameter J)
variable (hAD : ∀ (a : Multiplicative E) (d : FivePositive.Parameter J), Commute (r.A a) (r.D d))
variable (hCD : ∀ (c : Multiplicative E) (d : FivePositive.Parameter J), Commute (r.C c) (r.D d))
variable (hCA : ∀ (a c : E), r.C (Multiplicative.ofAdd c)*r.A (Multiplicative.ofAdd a) =
  r.A (Multiplicative.ofAdd a)*r.D (FivePositive.traceParameter J a c)*
    r.C (Multiplicative.ofAdd c))
variable (hBA : ∀ (a : E) (p : FivePositive.Parameter J), r.B p*r.A (Multiplicative.ofAdd a) =
  r.A (Multiplicative.ofAdd a)*r.D (T p a)*
    r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.B p)

include hAD hCD hCA hBA in
/-- Associativity of B(p) A(a) A(b) gives the first source functional equation at the level of the full Hermitian correction. -/
theorem correction_add (hD : Function.Injective r.D) (p : FivePositive.Parameter J) (a b : E) :
    T p (a+b) = T p a * FivePositive.traceParameter J b (a*J.conj p.val.2) * T p b := by
  have hAadd : r.A (Multiplicative.ofAdd (a+b)) =
      r.A (Multiplicative.ofAdd a)*r.A (Multiplicative.ofAdd b) := r.A.map_mul _ _
  have hCadd : r.C (Multiplicative.ofAdd ((a+b)*J.conj p.val.2)) =
      r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*
        r.C (Multiplicative.ofAdd (b*J.conj p.val.2)) := by
    rw [add_mul]
    exact r.C.map_mul _ _
  apply hD
  apply mul_left_cancel (a := r.A (Multiplicative.ofAdd (a+b)))
  apply mul_right_cancel (b := r.C (Multiplicative.ofAdd ((a+b)*J.conj p.val.2))*r.B p)
  calc
    _ = r.B p * r.A (Multiplicative.ofAdd (a+b)) := by rw [hBA]; simp only [mul_assoc]
    _ = (r.B p*r.A (Multiplicative.ofAdd a))*r.A (Multiplicative.ofAdd b) := by
      rw [hAadd, mul_assoc]
    _ = r.A (Multiplicative.ofAdd a)*r.D (T p a)*
        r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*
        (r.A (Multiplicative.ofAdd b)*r.D (T p b)*
          r.C (Multiplicative.ofAdd (b*J.conj p.val.2))*r.B p) := by
      rw [hBA a p]
      simp only [mul_assoc]
      rw [hBA b p]
      simp only [mul_assoc]
    _ = r.A (Multiplicative.ofAdd a)*r.D (T p a)*
        (r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.A (Multiplicative.ofAdd b))*
        r.D (T p b)*r.C (Multiplicative.ofAdd (b*J.conj p.val.2))*r.B p := by
      simp only [mul_assoc]
    _ = r.A (Multiplicative.ofAdd a)*
        (r.D (T p a)*r.A (Multiplicative.ofAdd b))*
        r.D (FivePositive.traceParameter J b (a*J.conj p.val.2))*
        (r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.D (T p b))*
        r.C (Multiplicative.ofAdd (b*J.conj p.val.2))*r.B p := by
      rw [hCA]; simp only [mul_assoc]
    _ = _ := by
      rw [(hAD _ _).eq.symm, (hCD _ _).eq]
      simp only [hAadd, hCadd, map_mul, mul_assoc]

include hAD hCD hCA hBA in
/-- The Hermitian multiplication law and its norm constraint give the scalar polarization identity. In this crossing convention the coefficient is p.val.2. -/
theorem coefficient_add (hD : Function.Injective r.D)
    (hfst : ∀ (p : FivePositive.Parameter J) (a : E), (T p a).val.1 = a*p.val.1)
    (p : FivePositive.Parameter J) (a b : E) :
    (T p (a+b)).val.2 = (T p a).val.2 + (T p b).val.2 +
      p.val.2*(a*J.conj b+b*J.conj a) := by
  have h := congrArg (fun q : FivePositive.Parameter J => q.val.2)
    (correction_add J r T hAD hCD hCA hBA hD p a b)
  change (T p (a+b)).val.2 =
    ((T p a).val.2 + (b*J.conj (a*J.conj p.val.2)+J.conj b*(a*J.conj p.val.2)) -
      (T p a).val.1*J.conj 0) + (T p b).val.2 -
      ((T p a).val.1+0)*J.conj (T p b).val.1 at h
  simp only [hfst, map_mul, map_zero, J.conj_involutive p.val.2, mul_zero,
    add_zero, CharTwo.sub_eq_add] at h
  have hp := FivePositive.parameter_relation J p
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h + a*J.conj b*hp

omit [CharP E 2] in
include hBA in
/-- Transporting the same crossing by an actual automorphism proves covariance of its unknown correction. -/
theorem correction_scale (hD : Function.Injective r.D) (t : E) (k : Y ≃* Y)
    (hA : ∀ a, k (r.A (Multiplicative.ofAdd a)) = r.A (Multiplicative.ofAdd (t*a)))
    (hB : ∀ p, k (r.B p) = r.B p)
    (hC : ∀ c, k (r.C (Multiplicative.ofAdd c)) = r.C (Multiplicative.ofAdd (t*c)))
    (hDt : ∀ p, k (r.D p) = r.D (FivePositive.normParameter J t p))
    (p : FivePositive.Parameter J) (a : E) :
    T p (t*a) = FivePositive.normParameter J t (T p a) := by
  apply hD
  apply mul_left_cancel (a := r.A (Multiplicative.ofAdd (t*a)))
  apply mul_right_cancel (b := r.C (Multiplicative.ofAdd ((t*a)*J.conj p.val.2))*r.B p)
  have he := congrArg k (hBA a p)
  simp only [map_mul, hA, hB, hC, hDt] at he
  calc
    _ = r.B p * r.A (Multiplicative.ofAdd (t*a)) := by rw [hBA]; simp only [mul_assoc]
    _ = _ := by simpa only [mul_assoc] using he

include hAD hCD hCA hBA in
/-- The ordinary-source torus action determines the entire correction, using only its previously known first coordinate. -/
theorem correction_eq_norm_of_torus (hD : Function.Injective r.D)
    (hfst : ∀ (p : FivePositive.Parameter J) (a : E), (T p a).val.1 = a*p.val.1)
    (θ : E) (hθ : θ+J.conj θ ≠ 0)
    (k : E → Y ≃* Y)
    (hA : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ a,
      k t (r.A (Multiplicative.ofAdd a)) = r.A (Multiplicative.ofAdd (t*a)))
    (hB : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ p, k t (r.B p) = r.B p)
    (hC : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ c,
      k t (r.C (Multiplicative.ofAdd c)) = r.C (Multiplicative.ofAdd (t*c)))
    (hDt : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ p,
      k t (r.D p) = r.D (FivePositive.normParameter J t p))
    (p : FivePositive.Parameter J) (a : E) : T p a = FivePositive.normParameter J a p := by
  apply Subtype.ext
  apply Prod.ext (hfst p a)
  exact norm_rigidity J.conj J.conj_involutive (fun b => (T p b).val.2) p.val.2 θ hθ
    (coefficient_add J r T hAD hCD hCA hBA hD hfst p)
    (fun t ht b => congrArg (fun q : FivePositive.Parameter J => q.val.2)
      (correction_scale J r T hBA hD t (k t) (hA t ht) (hB t ht) (hC t ht) (hDt t ht) p b)) a

include hCD hBA in
/-- Associativity of B(p) B(q) A(a) gives compatibility with multiplication in the nonabelian Hermitian group, the second source functional equation. -/
theorem correction_mul (hD : Function.Injective r.D)
    (hfst : ∀ (p : FivePositive.Parameter J) (a : E), (T p a).val.1 = a*p.val.1)
    (hBC : ∀ p c, Commute (r.B p) (r.C c))
    (hBD : ∀ p q, r.B p*r.D q = r.D q*
      r.C (Multiplicative.ofAdd (q.val.1*J.conj p.val.1))*r.B p)
    (p q : FivePositive.Parameter J) (a : E) : T (p*q) a = T p a*T q a := by
  have hc : a*J.conj (p*q).val.2 =
      a*J.conj p.val.2 + (T q a).val.1*J.conj p.val.1 + a*J.conj q.val.2 := by
    change a*J.conj (p.val.2+q.val.2-p.val.1*J.conj q.val.1) = _
    rw [CharTwo.sub_eq_add]
    simp only [map_add, map_mul, J.conj_involutive q.val.1, hfst]
    ring
  have hCmul : r.C (Multiplicative.ofAdd (a*J.conj (p*q).val.2)) =
      r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*
      r.C (Multiplicative.ofAdd ((T q a).val.1*J.conj p.val.1))*
      r.C (Multiplicative.ofAdd (a*J.conj q.val.2)) := by
    rw [hc]
    exact (r.C.map_mul _ _).trans (congrArg (fun z => z *
      r.C (Multiplicative.ofAdd (a*J.conj q.val.2))) (r.C.map_mul _ _))
  apply hD
  apply mul_left_cancel (a := r.A (Multiplicative.ofAdd a))
  apply mul_right_cancel (b := r.C (Multiplicative.ofAdd (a*J.conj (p*q).val.2))*r.B (p*q))
  calc
    _ = r.B (p*q)*r.A (Multiplicative.ofAdd a) := by rw [hBA]; simp only [mul_assoc]
    _ = r.B p * (r.B q * r.A (Multiplicative.ofAdd a)) := by rw [map_mul, mul_assoc]
    _ = (r.B p*r.A (Multiplicative.ofAdd a))*r.D (T q a)*
        r.C (Multiplicative.ofAdd (a*J.conj q.val.2))*r.B q := by
      rw [hBA]; simp only [mul_assoc]
    _ = r.A (Multiplicative.ofAdd a)*r.D (T p a)*
        r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*
        (r.B p*r.D (T q a))*r.C (Multiplicative.ofAdd (a*J.conj q.val.2))*r.B q := by
      rw [hBA]; simp only [mul_assoc]
    _ = r.A (Multiplicative.ofAdd a)*r.D (T p a)*
        (r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.D (T q a))*
        r.C (Multiplicative.ofAdd ((T q a).val.1*J.conj p.val.1))*
        (r.B p*r.C (Multiplicative.ofAdd (a*J.conj q.val.2)))*r.B q := by
      rw [hBD]; simp only [mul_assoc]
    _ = _ := by
      rw [(hCD _ _).eq, (hBC _ _).eq]
      simp only [map_mul, hCmul, mul_assoc]

include hAD hCD hCA hBA in
/-- Discharge the unknown mixed coefficient in the exact positive BC₂ presentation using source Cartan actions. -/
theorem relations_of_torus (hD : Function.Injective r.D)
    (hfst : ∀ (p : FivePositive.Parameter J) (a : E), (T p a).val.1 = a*p.val.1)
    (hBC : ∀ p c, Commute (r.B p) (r.C c))
    (hBD : ∀ p q, r.B p*r.D q = r.D q*
      r.C (Multiplicative.ofAdd (q.val.1*J.conj p.val.1))*r.B p)
    (θ : E) (hθ : θ+J.conj θ ≠ 0)
    (k : E → Y ≃* Y)
    (hA : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ a,
      k t (r.A (Multiplicative.ofAdd a)) = r.A (Multiplicative.ofAdd (t*a)))
    (hB : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ p, k t (r.B p) = r.B p)
    (hC : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ c,
      k t (r.C (Multiplicative.ofAdd c)) = r.C (Multiplicative.ofAdd (t*c)))
    (hDt : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ p,
      k t (r.D p) = r.D (FivePositive.normParameter J t p)) : FivePositive.Relations J r where
  AD := hAD
  CD := hCD
  BC := hBC
  CA := hCA
  BD := hBD
  BA a p := by
    rw [hBA, correction_eq_norm_of_torus J r T hAD hCD hCA hBA hD hfst θ hθ k hA hB hC hDt]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FiveCoefficients
