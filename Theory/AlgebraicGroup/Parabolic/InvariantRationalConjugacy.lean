module

public import Theory.AlgebraicGroup.Parabolic.InvariantRationalConjugacy.Descent

/-!
# Finite-parabolic application of rational descent

This is the assembly boundary for the reverse direction of GLS3 2.6.8.
The descent theorem constructs a conjugator in the actual prime-to-p residual,
and the theorem below applies it to the parent's literal finite-parabolic
predicate. Algebraic standard-position geometry, connected Lang surjectivity
and the fixed root-generation theorem are still explicit source inputs.
Their conditional application here does not establish the unconditional book
theorem.
-/

namespace Theory.AlgebraicGroup.InvariantRationalConjugacy

open FiniteParabolicRealization

variable {k : Type*} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]

/-- Apply the rational descent to the actual finite parabolic. This discharges
the reverse-correspondence step once the earlier geometric, Lang and finite
root-generation producers have supplied the displayed hypotheses. -/
public theorem isFiniteParabolic_restrict_of_descent_inputs
    (σ : AlgebraicEndomorphism K) (p : ℕ) [Fact p.Prime] [CharP k p]
    (B T Q : ClosedSubgroup K) (hTB : T ≤ B)
    (hB : B.toSubgroup.map σ.onPoints = B.toSubgroup)
    (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup)
    (hself : Q.normalizer = Q)
    (hstandard : ∃ g : Variety.Point K, B ≤ Q.conjugate g)
    (hunique : ∀ g h : Variety.Point K,
      B ≤ Q.conjugate g → B ≤ Q.conjugate h → Q.conjugate g = Q.conjugate h)
    (hLang : Function.Surjective (langMorphism (invariantRestriction σ Q hQ)).toFun)
    {ι : Type*} (Y : ι → ClosedSubgroup K)
    (hY : ∀ i, IsUnipotentAlgebraicGroup (Y i).carrierVariety)
    (hgen : T.toSubgroup.comap (fixedPoints σ).subtype ⊔
      (⨆ i, (Y i).toSubgroup.comap (fixedPoints σ).subtype) = ⊤) :
    IsFiniteParabolic σ p B (restrict σ p Q.toSubgroup) :=
  isFiniteParabolic_of_standard_conjugator σ p B Q
    (exists_residual_standard_conjugator σ p B T Q hTB hB hQ hself
      hstandard hunique hLang Y hY hgen)

end Theory.AlgebraicGroup.InvariantRationalConjugacy
