module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.ProjectiveData
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Lifting

/-!
# Comparing a lifted simple differential quotient with the original factor

Intertwining genuine rational group actions intertwines their canonical root
operators, by uniqueness of the scalar root-orbit polynomials. Consequently,
if a simple quotient of the infinitesimal highest-vector module has a rational
lift with the same integral basic highest weight, raw highest-weight uniqueness
identifies that lift with the original factor. Every subspace preserved by all
first-degree root operators is then zero or the whole space.

The simple quotient is constructed in `CyclicQuotient`. `Conjugation` proves
its conjugation data and full positive primitive line, and `Lifting` constructs
its rational lift with the exact integral highest weight. The final theorem
`rootOperatorInvariant_eq_bot_or_top` discharges both inputs to the conditional
comparison below. It uses only the inherited universal-version hypothesis,
raw highest-weight uniqueness, and the specified nonzero basic highest weight.
The reverse highest-weight contract is unnecessary. Group irreducibility is
never silently used as differential irreducibility, and no short-root density
or negative-word spanning hypothesis occurs.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), Curtis 2.7 and the lifting argument §§4.1–4.9;
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- An actual group intertwiner intertwines canonical root coefficients, even on different spaces. -/
theorem rootOperator_intertwines {B C : AlgebraicFactor F}
    (f : B.Space →ₗ[F] C.Space) (hf : Intertwines B.action C.action f)
    (r : F4Chevalley.Root) (w : B.Space) :
    f (EndNode.Multiplicity.rootOperator B r w) =
      EndNode.Multiplicity.rootOperator C r (f w) := by
  apply (Module.finBasis F C.Space).repr.injective
  ext i
  let l := (Module.finBasis F C.Space).coord i
  have hp : EndNode.Multiplicity.rootPolynomial B r (l.comp f) w =
      EndNode.Multiplicity.rootPolynomial C r l (f w) := by
    apply Polynomial.funext
    intro t
    simp only [EndNode.Multiplicity.rootPolynomial_eval, LinearMap.comp_apply]
    exact congrArg l (hf _ w)
  have hc := congrArg (fun q : Polynomial F => q.coeff 1) hp
  rw [← EndNode.Multiplicity.dual_rootOperator,
    ← EndNode.Multiplicity.dual_rootOperator] at hc
  exact hc

/-- Differential irreducibility transports across an actual group intertwiner. -/
theorem rootOperatorInvariant_of_equivalent {B C : AlgebraicFactor F}
    (e : B.Space ≃ₗ[F] C.Space) (he : Intertwines B.action C.action e.toLinearMap)
    (hirr : ∀ W : Submodule F C.Space,
      (∀ r w, w ∈ W → EndNode.Multiplicity.rootOperator C r w ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (p : RootExpansion B.action) (W : Submodule F B.Space)
    (hW : p.IsRootOperatorInvariant W) : W = ⊥ ∨ W = ⊤ := by
  have hm : ∀ r w, w ∈ W.map e.toLinearMap →
      EndNode.Multiplicity.rootOperator C r w ∈ W.map e.toLinearMap := by
    intro r w hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
    refine Submodule.mem_map.mpr ⟨p.coeff r 1 z, hW r z hz, ?_⟩
    rw [p.coeff_one_eq_rootOperator]
    exact rootOperator_intertwines e.toLinearMap he r z
  rcases hirr (W.map e.toLinearMap) hm with hbot | htop
  · left
    apply le_bot_iff.mp
    intro w hw
    have hz : e w = 0 := by
      have hm : e w ∈ W.map e.toLinearMap := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
      simpa only [hbot, Submodule.mem_bot] using hm
    exact e.injective (hz.trans e.map_zero.symm)
  · right
    apply top_unique
    intro w _
    have hm : e w ∈ W.map e.toLinearMap := by rw [htop]; trivial
    obtain ⟨z, hz, hez⟩ := Submodule.mem_map.mp hm
    exact e.injective hez ▸ hz

/-- Highest-weight uniqueness transfers the simplicity of a lifted quotient to the original factor. -/
theorem rootOperatorInvariant_eq_bot_or_top_of_lift
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    {B : AlgebraicFactor F} {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v)
    (Q : SimpleCyclicQuotient B v) (L : Q.RationalLift b)
    (p : RootExpansion B.action) (W : Submodule F B.Space)
    (hW : p.IsRootOperatorInvariant W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨e, he⟩ := hhigh B L.factor (basicCoefficient b) ⟨v, hv⟩ L.hasHighestWeight
  apply rootOperatorInvariant_of_equivalent e he _ p W hW
  intro U hU
  apply Q.operatorInvariant_eq_bot_or_top U
  intro r w hw
  have h := hU r w hw
  rwa [L.rootOperator_eq r] at h

/-- Construct the simple quotient and reduce all-root irreducibility to its rational lifting theorem. -/
theorem rootOperatorInvariant_eq_bot_or_top_of_lifting
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    {B : AlgebraicFactor F} {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v)
    (hlift : ∀ Q : SimpleCyclicQuotient B v, Nonempty (Q.RationalLift b))
    (p : RootExpansion B.action) (W : Submodule F B.Space)
    (hW : p.IsRootOperatorInvariant W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨Q⟩ := exists_simpleCyclicQuotient B hv.1
  obtain ⟨L⟩ := hlift Q
  exact rootOperatorInvariant_eq_bot_or_top_of_lift hhigh hv Q L p W hW

/-- The conjugation theorem and the conditional integration theorem may be
proved independently. Their combination discharges the lifting premise. -/
theorem rootOperatorInvariant_eq_bot_or_top_of_conjugation_and_lifting
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    {B : AlgebraicFactor F} {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v)
    (hconj : ∀ Q : SimpleCyclicQuotient B v, Nonempty Q.ConjugationData)
    (hlift : ∀ Q : SimpleCyclicQuotient B v, Q.ConjugationData → Nonempty (Q.RationalLift b))
    (p : RootExpansion B.action) (W : Submodule F B.Space)
    (hW : p.IsRootOperatorInvariant W) : W = ⊥ ∨ W = ⊤ := by
  apply rootOperatorInvariant_eq_bot_or_top_of_lifting hhigh hv _ p W hW
  intro Q
  obtain ⟨D⟩ := hconj Q
  exact hlift Q D

/-- Every subspace invariant under all first-degree root operators of a
nonzero basic factor is zero or the whole space. The conjugation and lifting
premises of the conditional bridge are proved here from the inherited source
hypotheses. The coefficients are those of the actual action, through
`RootExpansion.coeff_one_eq_rootOperator`. -/
theorem rootOperatorInvariant_eq_bot_or_top [CharP F 2]
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    {B : AlgebraicFactor F} {b : BasicWeight} (hb : b ≠ (0, 0)) {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v)
    (p : RootExpansion B.action) (W : Submodule F B.Space)
    (hW : p.IsRootOperatorInvariant W) : W = ⊥ ∨ W = ⊤ := by
  apply rootOperatorInvariant_eq_bot_or_top_of_conjugation_and_lifting hhigh hv
    (fun Q => Q.nonempty_conjugationData hU hv)
    (fun Q D => Q.nonempty_rationalLift_of_conjugation hU hb hv D) p W hW

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
