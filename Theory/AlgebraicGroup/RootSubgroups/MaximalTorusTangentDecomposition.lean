module

public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.RootSubgroups.TangentLieRootSpace

/-!
# Contracted maximal-torus tangent decompositions

The identity tangent of a reductive group with central torus is not, in
general, a Killing Lie algebra: its central tangent lies in the radical of the
Killing form.  Moreover, in positive characteristic a nontrivial torus
character can have zero differential, so a group-character weight space cannot
be identified with a Lie root space without an explicit faithfulness
hypothesis.  This module therefore exports the smallest sound comparison
interface.  The group-character weight decomposition is a characteristic-free
theorem supplied by
`maximalTorus_identityTangentRepresentation_weightSpace_iSup_eq_top`; faithful
character differentiation and the differentiated conjugation equation remain
the two explicit comparison inputs to the existing Lie-root-space equivalence.
The legacy three-part contract retains its spanning field for API stability,
and a public constructor now discharges that field automatically.

The geometric root-support step is kept equally explicit.  A tangent of the
centralizer is always fixed by the torus, hence has trivial group-character
weight.  The reverse inclusion is the exact infinitesimal-centralizer input.
For a nontrivial character, the comparison contract together with the
unconditional spanning theorem converts a nonzero
inverse-character weight space to a nonzero generalized Lie root space; an
explicit integrability hypothesis then realizes it by a one-parameter root
subgroup.  Under these two missing geometric hypotheses, the contract's
remaining inputs and the unconditional spanning theorem decompose the full
tangent into the embedded centralizer tangent and the inverse weights of actual
roots.  Thus central torus directions
remain visible rather than being hidden in a false full-tangent Killing claim.

These statements use the root definitions underlying GLS3 Definitions
1.9.1--1.9.3, but no clause of Theorems 1.9.5 or 1.10.1 and no unresolved
numbered theorem.  Reductivity and maximality provide the intended context;
they do not silently discharge the two explicit geometric hypotheses.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The explicit comparison contract for a maximal-torus identity tangent.

The first conjunct is faithful differentiation of torus characters, the
second is the spanning decomposition into group-character weight spaces, and
the third is the differentiated conjugation equation.  The spanning conjunct
is now automatic for a maximal torus and is retained here for compatibility;
`maximalTorusIdentityTangentRootDecomposition_of_comparison` constructs the
contract from the two remaining comparison inputs.
-/
public def MaximalTorusIdentityTangentRootDecomposition
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) : Prop :=
  Function.Injective (maximalTorusCartanCharacterDifferential T) ∧
    (⨆ χ : TorusWeight T,
      weightSpace (identityTangentRepresentation K) T χ) = ⊤ ∧
    IdentityTangentWeightBracketCompatibility T

/-- Construct the maximal-torus tangent comparison contract from its two
nonautomatic inputs. -/
public theorem maximalTorusIdentityTangentRootDecomposition_of_comparison
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T)
    (hdiff : Function.Injective
      (maximalTorusCartanCharacterDifferential T))
    (hbracket : IdentityTangentWeightBracketCompatibility T) :
    MaximalTorusIdentityTangentRootDecomposition T :=
  ⟨hdiff,
    maximalTorus_identityTangentRepresentation_weightSpace_iSup_eq_top K T hT,
    hbracket⟩

omit [IsAlgClosed k] in
/-- The embedded tangent of the torus centralizer has trivial character
weight.  Only the reverse inclusion needs a separate infinitesimal fixed-locus
or smooth-centralizer theorem. -/
public theorem centralizer_identityTangent_le_zeroWeight
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) :
    LinearMap.range
        (identityTangentMorphismLinearMap T.centralizer.inclusion) ≤
      weightSpace (identityTangentRepresentation K) T 1 := by
  rintro D hD
  obtain ⟨E, rfl⟩ := hD
  intro s
  apply Derivation.ext
  intro f
  have hone : (1 : TorusWeight T).pointCharacter s = 1 := rfl
  rw [hone, one_smul, identityTangentRepresentation_action_apply,
    identityTangentMorphismLinearMap_apply,
    identityTangentMorphismLinearMap_apply]
  change E (T.centralizer.inclusion.toVariety.pullbackAlgHom
      ((AlgebraicGroup.conjugationByMorphism K
        (T.includePoint s)).pullbackAlgHom f)) =
    E (T.centralizer.inclusion.toVariety.pullbackAlgHom f)
  apply congrArg E
  apply Variety.PolynomialFunction.ext
  intro x
  change f (T.includePoint s * T.centralizer.includePoint x *
      (T.includePoint s)⁻¹) = f (T.centralizer.includePoint x)
  congr 1
  have hx := Subgroup.mem_centralizer_iff.mp
    (T.centralizer.pointEquiv x).property
    (T.includePoint s) (T.pointEquiv s).property
  have hc : (T.centralizer.pointEquiv x).val =
      T.centralizer.includePoint x := rfl
  have hx' : T.includePoint s * T.centralizer.includePoint x =
      T.centralizer.includePoint x * T.includePoint s := by
    rw [hc] at hx
    exact hx
  rw [hx']
  simp

/-- The missing reverse inclusion for the zero group-character weight.
Together with `centralizer_identityTangent_le_zeroWeight`, this says exactly
that the zero weight is the embedded tangent of the torus centralizer. -/
@[expose]
public def IdentityTangentZeroWeightCentralizerExhaustion
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) : Prop :=
  weightSpace (identityTangentRepresentation K) T 1 ≤
    LinearMap.range
      (identityTangentMorphismLinearMap T.centralizer.inclusion)

/-- The precise geometric integrability input left after the contracted
weight-space/Lie-root-space comparison: every nonzero generalized Lie root
space at an inverse character is realized by an actual torus root. -/
@[expose]
public def MaximalTorusIdentityTangentLieRootIntegrability
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T) : Prop :=
  let _ : LieRing.IsNilpotent (maximalTorusCartan T) :=
    maximalTorusCartan_isNilpotent T hT
  ∀ alpha : TorusWeight T, alpha ≠ 1 →
    LieAlgebra.rootSpace (maximalTorusCartan T)
        (maximalTorusCartanCharacterDifferential T alpha⁻¹) ≠ ⊥ →
      IsTorusRoot T alpha

/-- Under the two remaining comparison hypotheses, each actual
torus-character weight space is the corresponding Lie root space.  The third
input of `inverseWeightSpaceRootSpaceEquiv`, character-weight spanning, is
unconditional. -/
public noncomputable def maximalTorus_identityTangent_rootSpace_equiv_of_contract
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T)
    (hcontract : MaximalTorusIdentityTangentRootDecomposition T)
    (chi : TorusWeight T) :
    let _ : LieRing.IsNilpotent (maximalTorusCartan T) :=
      maximalTorusCartan_isNilpotent T hT
    weightSpace (identityTangentRepresentation K) T chi⁻¹ ≃ₗ[k]
      LieAlgebra.rootSpace (maximalTorusCartan T)
        (maximalTorusCartanCharacterDifferential T chi⁻¹) := by
  exact inverseWeightSpaceRootSpaceEquiv T hT hcontract.1
    (maximalTorus_identityTangentRepresentation_weightSpace_iSup_eq_top K T hT)
    hcontract.2.2 chi

/-- The Lie-root-space integrability hypothesis exhausts all nontrivial
inverse-character tangent weights by actual roots. -/
public theorem identityTangent_rootSupport_of_lieRootIntegrability
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T)
    (hcontract : MaximalTorusIdentityTangentRootDecomposition T)
    (hintegrable : MaximalTorusIdentityTangentLieRootIntegrability T hT) :
    ∀ alpha : TorusWeight T,
      weightSpace (identityTangentRepresentation K) T alpha⁻¹ ≠ ⊥ →
      alpha ≠ 1 → IsTorusRoot T alpha := by
  let _ : LieRing.IsNilpotent (maximalTorusCartan T) :=
    maximalTorusCartan_isNilpotent T hT
  intro alpha hweight halpha
  apply hintegrable alpha halpha
  have e :
      weightSpace (identityTangentRepresentation K) T alpha⁻¹ ≃ₗ[k]
        LieAlgebra.rootSpace (maximalTorusCartan T)
          (maximalTorusCartanCharacterDifferential T alpha⁻¹) :=
    maximalTorus_identityTangent_rootSpace_equiv_of_contract
      T hT hcontract alpha
  obtain ⟨v, hv, hvne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hweight
  let v' : weightSpace (identityTangentRepresentation K) T alpha⁻¹ := ⟨v, hv⟩
  have hv'ne : v' ≠ 0 := by
    intro hv'zero
    apply hvne
    exact congrArg Subtype.val hv'zero
  have hevne : e v' ≠ 0 :=
    (LinearEquiv.map_eq_zero_iff e).not.mpr hv'ne
  intro hroot
  have hevzero : (e v' : IdentityPointDerivation K) = 0 :=
    (LieSubmodule.eq_bot_iff _).mp hroot _ (e v').property
  apply hevne
  apply Subtype.ext
  exact hevzero

/-- In the reductive maximal-torus setting, the explicit zero-weight
centralizer exhaustion and Lie-root integrability hypotheses give the smallest
currently sound full identity-tangent support theorem.

The first conclusion identifies the trivial group-character weight with the
embedded tangent of the centralizer.  The second says that every nontrivial
identity-tangent weight is the inverse of an actual torus root.  The final
spanning equality keeps the centralizer summand explicit and uses the
unconditional maximal-torus identity-tangent weight decomposition. -/
public theorem reductive_maximalTorus_identityTangent_rootSupport_and_zeroWeight_of_contract
    {K : Variety k} [AlgebraicGroup K]
    (_hK : IsReductiveAlgebraicGroup K)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T)
    (hcontract : MaximalTorusIdentityTangentRootDecomposition T)
    (hzero : IdentityTangentZeroWeightCentralizerExhaustion T)
    (hintegrable : MaximalTorusIdentityTangentLieRootIntegrability T hT) :
    weightSpace (identityTangentRepresentation K) T 1 =
        LinearMap.range
          (identityTangentMorphismLinearMap T.centralizer.inclusion) ∧
      (∀ chi : TorusWeight T,
        weightSpace (identityTangentRepresentation K) T chi ≠ ⊥ →
        chi ≠ 1 → IsTorusRoot T chi⁻¹) ∧
      LinearMap.range
          (identityTangentMorphismLinearMap T.centralizer.inclusion) ⊔
        (⨆ alpha : {chi : TorusWeight T // chi ∈ TorusRootSet T},
          weightSpace (identityTangentRepresentation K) T alpha.1⁻¹) = ⊤ := by
  have hzeroEq : weightSpace (identityTangentRepresentation K) T 1 =
      LinearMap.range
        (identityTangentMorphismLinearMap T.centralizer.inclusion) :=
    le_antisymm hzero (centralizer_identityTangent_le_zeroWeight T)
  have hsupportRoot : ∀ alpha : TorusWeight T,
      weightSpace (identityTangentRepresentation K) T alpha⁻¹ ≠ ⊥ →
      alpha ≠ 1 → IsTorusRoot T alpha :=
    identityTangent_rootSupport_of_lieRootIntegrability
      T hT hcontract hintegrable
  have hsupportWeight : ∀ chi : TorusWeight T,
      weightSpace (identityTangentRepresentation K) T chi ≠ ⊥ →
      chi ≠ 1 → IsTorusRoot T chi⁻¹ := by
    intro chi hweight hchi
    apply hsupportRoot chi⁻¹
    · simpa only [inv_inv] using hweight
    · intro hinvOne
      apply hchi
      rw [← inv_inv chi, hinvOne, inv_one]
  refine ⟨hzeroEq, hsupportWeight, ?_⟩
  apply top_unique
  rw [← maximalTorus_identityTangentRepresentation_weightSpace_iSup_eq_top K T hT]
  refine iSup_le fun chi => ?_
  by_cases hchi : chi = 1
  · subst chi
    rw [hzeroEq]
    exact le_sup_left
  by_cases hweight :
      weightSpace (identityTangentRepresentation K) T chi = ⊥
  · rw [hweight]
    exact bot_le
  let alpha : {psi : TorusWeight T // psi ∈ TorusRootSet T} :=
    ⟨chi⁻¹, hsupportWeight chi hweight hchi⟩
  have hinv : alpha.1⁻¹ = chi := by
    change chi⁻¹⁻¹ = chi
    exact inv_inv chi
  rw [← hinv]
  exact le_trans
    (le_iSup
      (fun beta : {psi : TorusWeight T // psi ∈ TorusRootSet T} =>
        weightSpace (identityTangentRepresentation K) T beta.1⁻¹) alpha)
    le_sup_right

end Theory.AlgebraicGroup
