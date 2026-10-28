module
public import CFSG.Quasithin.ChapterF.Section09.ConjugatePair.Action

/-!
# The orthogonal action on the entire original F.9 closure

When the original U_H is a quaternion central product, its square action
has exactly the original Q_H kernel. Restriction to each subgroup of H
therefore identifies its original starred image with the actual orthogonal
range. Unlike the general pair-seed construction, this uses the already
identified whole closure and needs no intersecting-pair hypothesis.

Source application: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

/-- The actual closure action, restricted to any original subgroup of H. -/
noncomputable def closureOrthogonalAction (I : Subgroup G) (hIH : I≤D.H)
    (q : QuaternionCentralProductData D.UH) : I→*BinaryFourPlus.Wreath :=
  seedOrthogonalAction I D.UH (hIH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H)) q

theorem closureOrthogonalAction_ker (I : Subgroup G) (hIH : I≤D.H)
    (q : QuaternionCentralProductData D.UH)
    (hz : (center D.UH).map D.UH.subtype=D.V₁) :
    (closureOrthogonalAction I hIH q).ker=D.QH.subgroupOf I := by
  rw [closureOrthogonalAction,seedOrthogonalAction_ker I D.UH D.V₁ _ q hz
    (hIH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))]
  ext x
  change (x:G)∈commutatorPreimage I D.UH D.V₁↔(x:G)∈D.QH
  rw [mem_commutatorPreimage_iff _ _ _
    (hIH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))]
  simp only [x.property,true_and]
  constructor
  · intro hx
    rw [←h.kernel_UH_eq_QH]
    apply (h.mem_kernel_iff h.UH_le_H).mpr
    refine ⟨hIH x.property,fun u hu=>?_⟩
    rw [←commutatorElement_inv]
    exact D.V₁.inv_mem (hx u hu)
  · intro hx u hu
    rw [←commutatorElement_inv]
    exact D.V₁.inv_mem (h.commutator_UH_QH_le_point (commutator_mem_commutator hu hx))

noncomputable def closureOrthogonalEquiv (I : Subgroup G) (hIH : I≤D.H)
    (q : QuaternionCentralProductData D.UH)
    (hz : (center D.UH).map D.UH.subtype=D.V₁) :
    ((I.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) ≃*
      (closureOrthogonalAction I hIH q).range :=
  (MulEquiv.subgroupCongr (pairProjection_range I hIH).symm).trans
    (rangeEquivOfKerEq (pairProjection I hIH) (closureOrthogonalAction I hIH q)
      ((pairProjection_ker I hIH).trans (h.closureOrthogonalAction_ker I hIH q hz).symm))

theorem closureOrthogonalAction_H_ker (q : QuaternionCentralProductData D.UH)
    (hz : (center D.UH).map D.UH.subtype=D.V₁) :
    (closureOrthogonalAction D.H le_rfl q).ker=pCore 2 D.H :=
  (h.closureOrthogonalAction_ker D.H le_rfl q hz).trans
    (comap_map_eq_self_of_injective D.H.subtype_injective _)

noncomputable def closureStarEmbedding (q : QuaternionCentralProductData D.UH)
    (hz : (center D.UH).map D.UH.subtype=D.V₁) :
    (D.H ⧸ pCore 2 D.H)→*BinaryFourPlus.Wreath :=
  (closureOrthogonalAction D.H le_rfl q).range.subtype.comp
    (((QuotientGroup.quotientMulEquivOfEq (h.closureOrthogonalAction_H_ker q hz).symm).trans
      (QuotientGroup.quotientKerEquivRange (closureOrthogonalAction D.H le_rfl q))).toMonoidHom)

theorem closureStarEmbedding_mk (q : QuaternionCentralProductData D.UH)
    (hz : (center D.UH).map D.UH.subtype=D.V₁) (x : D.H) :
    h.closureStarEmbedding q hz (QuotientGroup.mk' (pCore 2 D.H) x)=
      closureOrthogonalAction D.H le_rfl q x := rfl

theorem closureStarEmbedding_injective (q : QuaternionCentralProductData D.UH)
    (hz : (center D.UH).map D.UH.subtype=D.V₁) :
    Function.Injective (h.closureStarEmbedding q hz) :=
  Subtype.val_injective.comp
    (((QuotientGroup.quotientMulEquivOfEq (h.closureOrthogonalAction_H_ker q hz).symm).trans
      (QuotientGroup.quotientKerEquivRange (closureOrthogonalAction D.H le_rfl q))).injective)

end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
end
