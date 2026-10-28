module

public import Theory.AlgebraicGroup.Parabolic.InvariantRationalConjugacy.Descent
public import Theory.AlgebraicGroup.Parabolic.InvariantRationalConjugacy.ConnectedLang.Reduction

/-!
# Connected Lang input for invariant parabolic descent

Apply the shorter connected Lang argument to the literal regular restriction
constructed in `Descent`. Exact invariance makes that restriction Steinberg.
The resulting solutions discharge the Lang premise of residual standard-position
descent, with the same quotient, point embedding and conjugation conventions.

The two geometric inputs of Steinberg 7.3 remain explicit here. Their proofs
must be supplied before this module establishes the unconditional Lang input.
Connectedness is the permitted input from standard-parabolic geometry.

Source: GLS3, Theorems 2.1.1 and 2.1.5(a), and Steinberg 7.2–7.3 and 10.8.
-/

universe u

namespace Theory.AlgebraicGroup.InvariantRationalConjugacy

open FiniteParabolicRealization

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

/-- Conditional connected Lang on the exact invariant restriction consumed
by rational descent. Semisimplicity of the ambient group is unnecessary. -/
public theorem invariantRestriction_lang_of_borel_geometry
    (σ : AlgebraicEndomorphism K) (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (Q : ClosedSubgroup K) (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup)
    (hconnected : Variety.IsConnected Q.carrierVariety)
    (hclosed : ConnectedLang.BorelLangClosedImages Q.carrierVariety)
    (hdense : ConnectedLang.BorelLangDominantImages Q.carrierVariety) :
    Function.Surjective (langMorphism (invariantRestriction σ Q hQ)).toFun :=
  ConnectedLang.lang_surjective_of_borel_geometry (invariantRestriction σ Q hQ)
    (invariantRestriction_steinberg σ hσ Q hQ) hconnected hclosed hdense

/-- The residual-conjugator consumer with its Lang premise discharged from
the two Borel-geometric inputs on the connected invariant parabolic.
The independent fixed-root generation input is retained exactly as in `Descent`. -/
public theorem exists_residual_standard_conjugator_of_borel_geometry
    (σ : AlgebraicEndomorphism K) (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (p : ℕ) [Fact p.Prime] [CharP k p] (B T Q : ClosedSubgroup K)
    (hTB : T ≤ B)
    (hB : B.toSubgroup.map σ.onPoints = B.toSubgroup)
    (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup)
    (hconnected : Variety.IsConnected Q.carrierVariety)
    (hself : Q.normalizer = Q)
    (hstandard : ∃ g : Variety.Point K, B ≤ Q.conjugate g)
    (hunique : ∀ g h : Variety.Point K,
      B ≤ Q.conjugate g → B ≤ Q.conjugate h → Q.conjugate g = Q.conjugate h)
    (hclosed : ConnectedLang.BorelLangClosedImages Q.carrierVariety)
    (hdense : ConnectedLang.BorelLangDominantImages Q.carrierVariety)
    {ι : Type*} (Y : ι → ClosedSubgroup K)
    (hY : ∀ i, IsUnipotentAlgebraicGroup (Y i).carrierVariety)
    (hgen : T.toSubgroup.comap (fixedPoints σ).subtype ⊔
      (⨆ i, (Y i).toSubgroup.comap (fixedPoints σ).subtype) = ⊤) :
    ∃ g : definingGroup σ p, B ≤ Q.conjugate (pointEmbedding σ p g) :=
  exists_residual_standard_conjugator σ p B T Q hTB hB hQ hself hstandard hunique
    (invariantRestriction_lang_of_borel_geometry σ hσ Q hQ hconnected hclosed hdense)
    Y hY hgen

end Theory.AlgebraicGroup.InvariantRationalConjugacy
