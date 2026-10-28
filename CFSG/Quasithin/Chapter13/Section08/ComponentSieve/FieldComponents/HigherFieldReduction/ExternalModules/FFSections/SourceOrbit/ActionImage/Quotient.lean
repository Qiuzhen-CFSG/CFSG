module

public import Theory.Representation.BinaryOffender.IrreducibleCentralSeed
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Faithful images before and after removing central vectors

For an invariant Irr⁺ constituent of a normal quasisimple K, the actions on
I and the literal quotient I/C_I(K) have exactly the same kernel. The quotient
kernel does not contain K, so the component normal-subgroup dichotomy makes
it centralize K. Its displacements are K-fixed, and it consequently fixes
[I,K] = I. The first isomorphism theorem identifies the two action images.

The quotient map intertwines this actual group isomorphism. Offender ranks
are therefore unchanged, while fixed codimensions decrease. This proves FF
descent without assuming faithfulness of either original group action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.18(3–4),
printed pp.325–326, and the use of B.4.2 in 13.8.20, printed pp.954–955.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Quotient
universe u
variable {G V : Type u} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
  (I : Subrepresentation ρ) (hI : IsIrrPlus ρ K I.toSubmodule)

abbrev quotientAction := normalCentralQuotient ρ K I

def quotientMap : I.toSubmodule →ₗ[ZMod 2] centralQuotient ρ K I.toSubmodule :=
  ((fixedSpace ρ K).comap I.toSubmodule.subtype).mkQ

theorem quotientMap_equivariant (g : G) (v : I.toSubmodule) :
    quotientMap ρ K I (I.toRepresentation g v) =
      quotientAction ρ K I g (quotientMap ρ K I v) := rfl

include hI in
theorem component_survives : ¬ K ≤ (actionHom (quotientAction ρ K I)).ker := by
  intro hk
  apply hI.not_le_fixedSpace ρ
  rw [← hI.choose_spec.1]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hkK, v, hv, rfl⟩
  have hfix := (actionHom_eq_one_iff _ k).mp (hk hkK)
    (Submodule.Quotient.mk (⟨v, hv⟩ : I.toSubmodule))
  exact (Submodule.Quotient.eq ((fixedSpace ρ K).comap I.toSubmodule.subtype)).mp hfix

variable [IsQuasisimple K]

include hI in
theorem quotient_kernel_centralizes :
    (actionHom (quotientAction ρ K I)).ker ≤ centralizer (K : Set G) := by
  have hc : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal, inferInstance⟩
  have hcomm := (hc.normal_dichotomy (actionHom (quotientAction ρ K I)).ker).resolve_left
    (component_survives ρ K I hI)
  exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hcomm)

include hI in
theorem quotient_kernel_eq :
    (actionHom (quotientAction ρ K I)).ker = (actionHom I.toRepresentation).ker := by
  apply le_antisymm
  · intro g hg
    have hc := quotient_kernel_centralizes ρ K I hI hg
    have hd (v : V) (hv : v ∈ I.toSubmodule) : ρ g v - v ∈ fixedSpace ρ K := by
      have hfix := (actionHom_eq_one_iff _ g).mp hg
        (Submodule.Quotient.mk (⟨v, hv⟩ : I.toSubmodule))
      exact (Submodule.Quotient.eq ((fixedSpace ρ K).comap I.toSubmodule.subtype)).mp hfix
    have hf : subspaceCommutator ρ I.toSubmodule K ≤ LinearMap.ker (ρ g - LinearMap.id) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, v, hv, rfl⟩
      have he : ρ g (ρ k v) = ρ k (ρ g v) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        rw [((mem_centralizer_iff.mp hc) k hk)]
      have hx := hd v hv ⟨k, hk⟩
      change ρ k (ρ g v - v) = ρ g v - v at hx
      change ρ g (ρ k v - v) - (ρ k v - v) = 0
      rw [map_sub] at hx
      rw [map_sub, he]
      exact sub_eq_zero.mpr ((sub_eq_sub_iff_sub_eq_sub).mp hx)
    apply (actionHom_eq_one_iff _ g).mpr
    intro v
    apply Subtype.ext
    exact sub_eq_zero.mp (hf (hI.choose_spec.1.symm ▸ v.property))
  · intro g hg
    apply (actionHom_eq_one_iff _ g).mpr
    intro v
    induction v using Submodule.Quotient.induction_on with | _ v =>
    exact congrArg (quotientMap ρ K I) ((actionHom_eq_one_iff _ g).mp hg v)

def imageEquiv : actionImage I.toRepresentation ≃* actionImage (quotientAction ρ K I) :=
  (QuotientGroup.quotientKerEquivOfSurjective (actionHom I.toRepresentation)
    I.toRepresentation.asGroupHom.rangeRestrict_surjective).symm.trans
  ((QuotientGroup.quotientMulEquivOfEq (quotient_kernel_eq ρ K I hI).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (actionHom (quotientAction ρ K I))
      (quotientAction ρ K I).asGroupHom.rangeRestrict_surjective))

theorem imageEquiv_actionHom (g : G) :
    imageEquiv ρ K I hI (actionHom I.toRepresentation g) =
      actionHom (quotientAction ρ K I) g := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (actionHom I.toRepresentation)
      I.toRepresentation.asGroupHom.rangeRestrict_surjective).symm
      (actionHom I.toRepresentation g) = QuotientGroup.mk g := by
    apply (MulEquiv.symm_apply_eq _).mpr
    rfl
  unfold imageEquiv
  dsimp only [MulEquiv.trans_apply]
  rw [h]
  rfl

theorem imageEquiv_equivariant (g : actionImage I.toRepresentation) (v : I.toSubmodule) :
    quotientMap ρ K I (imageRepresentation I.toRepresentation g v) =
      imageRepresentation (quotientAction ρ K I) (imageEquiv ρ K I hI g)
        (quotientMap ρ K I v) := by
  obtain ⟨g, rfl⟩ := I.toRepresentation.asGroupHom.rangeRestrict_surjective g
  change quotientMap ρ K I (imageRepresentation I.toRepresentation (actionHom I.toRepresentation g) v) =
    imageRepresentation (quotientAction ρ K I) (imageEquiv ρ K I hI (actionHom I.toRepresentation g)) _
  rw [imageEquiv_actionHom]
  rfl

variable [Finite V]

include hI in
theorem quotient_ff (hff : IsFFModule (imageRepresentation I.toRepresentation)) :
    IsFFModule (imageRepresentation (quotientAction ρ K I)) := by
  let e := imageEquiv ρ K I hI
  let σ := imageRepresentation (quotientAction ρ K I)
  obtain ⟨A, hA, hbound⟩ := hff
  have hcod := fixedCodim_le_of_equivariant_surjection
    (imageRepresentation I.toRepresentation) (σ.comp e.toMonoidHom)
    (quotientMap ρ K I) (Submodule.mkQ_surjective _)
    (imageEquiv_equivariant ρ K I hI) A
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨A.map e.toMonoidHom, ⟨?_, IsElementaryAbelian.map e.toMonoidHom⟩, ?_⟩
  · intro hb
    exact hA.1 ((A.map_eq_bot_iff_of_injective e.injective).mp hb)
  · rw [rank_map_injective _ e.injective]
    have heq := fixedSpace_comp_map σ e.toMonoidHom A
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (σ.comp e.toMonoidHom) A) ≤ _ at hcod
    rw [heq] at hcod
    exact hcod.trans hbound
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Quotient

