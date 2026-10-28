module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentLines
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound

/-!
# Tangent spanning for the literal F4 carrier

The canonical root tangents are independent because they have distinct torus
characters. Their span is disjoint from the fixed tangent space, and the
embedded tangent of the split torus lies in that fixed space. Consequently an
upper bound on the carrier tangent dimension by the torus tangent dimension
plus the number of roots forces the concrete tangent summands to span.

The reverse dimension inequality and the exact dimension of the known
summands are proved without geometric premises. In characteristic two, the
concrete Bruhat parametrizations give the upper bound via the geometric
dimension of the carrier. Applying the numerical reduction proves spanning
over every algebraically closed field of characteristic two, hence over the
algebraic closure of every finite field of characteristic two. Semisimplicity
and maximality of the split torus are not needed for this concrete conclusion.

This is the numerical reduction for the concrete F4 instance of GLS3,
Theorem 1.9.5(b), `refs/KGroup/GLS3/Chapter1.tex`. The character-independence
argument follows the analogous G2 construction in
`Theory/AlgebraicGroup/RootSystems/G2ChevalleyTorusRootSupport.lean`.
-/

public section

namespace Theory.AlgebraicGroup.F4Chevalley
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable section

local instance : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
  (splitTorus (k := k)).carrierAlgebraicGroup

/-- The literal root tangent vectors are linearly independent. -/
theorem concreteRootTangents_linearIndependent :
    LinearIndependent k (concreteRootTangent (k := k)) := by
  let w : Root → TorusWeight (splitTorus (k := k)) := fun r => (rootWeight r)⁻¹
  let p : Root → Submodule k (IdentityPointDerivation (Carrier (k := k))) :=
    fun r => weightSpace (identityTangentRepresentation (Carrier (k := k))) splitTorus (w r)
  have hw : Function.Injective w := by
    intro r s h
    exact concreteRootWeight_injective (inv_injective h)
  have hp : iSupIndep p :=
    (weightSpace_iSupIndep (identityTangentRepresentation (Carrier (k := k)))
      splitTorus).comp hw
  exact iSupIndep.linearIndependent p hp
    (fun r => (concreteRootTangent_isWeightVector r).2)
    (fun r => (concreteRootTangent_isWeightVector r).1)

/-- The subspace spanned by the literal root tangents. -/
@[expose] def concreteRootTangentSpan :
    Submodule k (IdentityPointDerivation (Carrier (k := k))) :=
  Submodule.span k (Set.range (concreteRootTangent (k := k)))

theorem concreteRootTangentSpan_finrank :
    Module.finrank k (concreteRootTangentSpan (k := k)) = Fintype.card Root :=
  finrank_span_eq_card concreteRootTangents_linearIndependent

/-- Independence of distinct characters makes the fixed space disjoint
from all the literal root tangent directions. -/
theorem concreteFixedTangent_disjoint_rootTangentSpan :
    Disjoint (concreteTangentSummand (k := k) none) concreteRootTangentSpan := by
  have hd := weightSpace_iSupIndep
    (identityTangentRepresentation (Carrier (k := k))) (splitTorus (k := k)) 1
  apply hd.mono_right
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  have hr : (rootWeight (k := k) r)⁻¹ ≠ 1 :=
    inv_ne_one.mpr (concreteRootWeight_ne_one r)
  have hle : weightSpace (identityTangentRepresentation (Carrier (k := k))) splitTorus
      (rootWeight r)⁻¹ ≤
      ⨆ χ : TorusWeight (splitTorus (k := k)), ⨆ (_ : χ ≠ 1),
        weightSpace (identityTangentRepresentation (Carrier (k := k))) splitTorus χ :=
    le_iSup_of_le ((rootWeight r)⁻¹) (le_iSup_of_le hr le_rfl)
  exact hle (concreteRootTangent_isWeightVector r).2

/-- Recombine the fixed space and root span using the shared summands. -/
theorem concreteTangentSummand_iSup_eq_fixed_sup_rootSpan :
    (⨆ i, concreteTangentSummand (k := k) i) =
      concreteTangentSummand none ⊔ concreteRootTangentSpan := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    cases i with
    | none => exact le_sup_left
    | some r =>
      apply le_trans _ le_sup_right
      exact Submodule.span_mono (by rintro _ (rfl : _ = concreteRootTangent r); exact ⟨r, rfl⟩)
  · apply sup_le
    · exact le_iSup concreteTangentSummand none
    · apply Submodule.span_le.mpr
      rintro _ ⟨r, rfl⟩
      exact (le_iSup concreteTangentSummand (some r))
        (Submodule.subset_span (Set.mem_singleton _))

/-- The dimension contributed by the known tangent directions. -/
theorem concreteTangentSummand_iSup_finrank :
    Module.finrank k ↥(⨆ i, concreteTangentSummand (k := k) i) =
      Module.finrank k (concreteTangentSummand (k := k) none) + Fintype.card Root := by
  rw [concreteTangentSummand_iSup_eq_fixed_sup_rootSpan]
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (concreteTangentSummand (k := k) none) (concreteRootTangentSpan (k := k))
  rw [concreteFixedTangent_disjoint_rootTangentSpan.eq_bot,
    finrank_bot, add_zero, concreteRootTangentSpan_finrank] at h
  exact h

/-- The actual embedded tangent of the split torus. -/
@[expose] def concreteTorusTangentRange :
    Submodule k (IdentityPointDerivation (Carrier (k := k))) :=
  LinearMap.range (identityTangentMorphismLinearMap (splitTorus (k := k)).inclusion)

theorem concreteTorusTangentRange_finrank :
    Module.finrank k (concreteTorusTangentRange (k := k)) =
      Module.finrank k (IdentityPointDerivation (splitTorus (k := k)).carrierVariety) :=
  LinearMap.finrank_range_of_inj
    (identityTangentMorphismLinearMap_inclusion_injective (splitTorus (k := k)))

/-- The torus fixes its own embedded identity tangent by conjugation. -/
theorem concreteTorusTangentRange_le_fixed :
    concreteTorusTangentRange (k := k) ≤ concreteTangentSummand none := by
  rintro D ⟨E, rfl⟩
  intro s
  apply Derivation.ext
  intro f
  have hone : (1 : TorusWeight (splitTorus (k := k))).pointCharacter s = 1 := rfl
  rw [hone, one_smul, identityTangentRepresentation_action_apply,
    identityTangentMorphismLinearMap_apply, identityTangentMorphismLinearMap_apply]
  change E ((splitTorus (k := k)).inclusion.toVariety.pullbackAlgHom
      ((AlgebraicGroup.conjugationByMorphism (Carrier (k := k))
        ((splitTorus (k := k)).includePoint s)).pullbackAlgHom f)) =
    E ((splitTorus (k := k)).inclusion.toVariety.pullbackAlgHom f)
  apply congrArg E
  apply Variety.PolynomialFunction.ext
  intro x
  change f ((splitTorus (k := k)).includePoint s *
      (splitTorus (k := k)).includePoint x *
      ((splitTorus (k := k)).includePoint s)⁻¹) =
    f ((splitTorus (k := k)).includePoint x)
  congr 1
  have hcomm : (splitTorus (k := k)).includePoint s *
      (splitTorus (k := k)).includePoint x =
        (splitTorus (k := k)).includePoint x * (splitTorus (k := k)).includePoint s := by
    have hcommT := (splitTorus_isSubtorus (k := k)).isMulCommutative
    rw [isMulCommutative_iff] at hcommT
    exact congrArg (splitTorus (k := k)).inclusion.onPoints (hcommT s x)
  rw [hcomm]
  simp

/-- A numerical tangent-dimension bound suffices for the concrete spanning
identity. The dimension bound is an explicit geometric premise. -/
theorem concreteTangentSummand_iSup_eq_top_of_finrank_le
    (hdim : Module.finrank k (IdentityPointDerivation (Carrier (k := k))) ≤
      Module.finrank k (IdentityPointDerivation (splitTorus (k := k)).carrierVariety) +
        Fintype.card Root) :
    (⨆ i, concreteTangentSummand (k := k) i) = ⊤ := by
  rw [concreteTangentSummand_iSup_eq_fixed_sup_rootSpan]
  apply Submodule.eq_top_of_disjoint
  · rw [concreteRootTangentSpan_finrank]
    apply hdim.trans
    apply Nat.add_le_add_right
    rw [← concreteTorusTangentRange_finrank]
    exact Submodule.finrank_mono concreteTorusTangentRange_le_fixed
  · exact concreteFixedTangent_disjoint_rootTangentSpan

/-- The torus and root directions already give the reverse numerical bound. -/
theorem concreteTorusTangent_finrank_add_card_root_le :
    Module.finrank k (IdentityPointDerivation (splitTorus (k := k)).carrierVariety) +
        Fintype.card Root ≤
      Module.finrank k (IdentityPointDerivation (Carrier (k := k))) := by
  calc
    _ ≤ Module.finrank k (concreteTangentSummand (k := k) none) + Fintype.card Root := by
      apply Nat.add_le_add_right
      rw [← concreteTorusTangentRange_finrank]
      exact Submodule.finrank_mono concreteTorusTangentRange_le_fixed
    _ = Module.finrank k ↥(⨆ i, concreteTangentSummand (k := k) i) :=
      concreteTangentSummand_iSup_finrank.symm
    _ ≤ _ := Submodule.finrank_le _

/-- The full fixed tangent space and the literal root tangent lines span the
identity tangent of the F4 carrier in characteristic two. The geometric
dimension bound discharges the last premise of the numerical reduction.
In particular this gives the spanning equality over the algebraic closure of
a finite characteristic-two field under the source semisimplicity and
maximal-torus hypotheses, without needing either hypothesis here. -/
theorem concreteTangentSummand_iSup_eq_top [CharP k 2] :
    (⨆ i : Option Root, concreteTangentSummand (k := k) i) = ⊤ :=
  concreteTangentSummand_iSup_eq_top_of_finrank_le
    concreteIdentityTangent_finrank_le_torus_add_card_root

end
end Theory.AlgebraicGroup.F4Chevalley
