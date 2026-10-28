module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticInputs
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSBlockFrattini

/-!
# Transport from the original action image to the intrinsic component quotient

Once the centralizer of the Omega orbit is identified with the ambient
two-core, restriction of the quotient map has kernel exactly the component's
two-core, by subnormality. Its first isomorphism theorem transports the given
Sp4(4) marking to the quotient used by the MS results. The Frattini-small
consumer below applies this transport to the actual generation-two overgroup.
It does not discharge the kernel identification or the non-Frattini branch.

Source: Aschbacher--Smith 9.3.6--10, printed pp.733--734; C.1.32 and
Meierfrankenfeld--Stellmacher (1993), the first split in (3.6).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

include c in
/-- The H-star member already supplies the outside-maximal standing guard. -/
theorem hasMaximalOutside : Chapter3.HasMaximalOutside T D.maximalLocal := by
  have hHcore : pCore 2 c.H ≠ ⊥ := by
    intro hb
    apply c.hstar.1.1.1
    change (pCore 2 c.H).map c.H.subtype = ⊥
    rw [hb, Subgroup.map_bot]
  obtain ⟨M, hM, hHM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot c.H hHcore
  exact Chapter3.hasMaximalOutside_of_two_distinct
    (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1 hM
    (le_normalizer_componentOrbit L T) (c.hstar.1.1.2.trans hHM)
    (fun he => c.hstar.1.2 (he ▸ hHM))

/-- The actual original overgroup has self-centralizing two-core and trivial center. -/
theorem fitting_center :
    generalizedFitting c.M = pCore 2 c.M ∧ center c.M = ⊥ := by
  obtain ⟨_, _, hf, hz, _⟩ := c.fourField_models c.hasMaximalOutside
  exact ⟨hf, hz⟩

/-- Restriction of the original action map, after identifying its ambient kernel. -/
theorem residual_action_kernel
    (hr : IsPReduced 2
      (omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)))
    (hker : centralizer (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M) : Set c.M) =
        pCore 2 c.M) :
    letI := hr.normal
    ((actionMk (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M))).subgroupMap
        (pResidual 2 c.M)).ker = pCore 2 (pResidual 2 c.M) := by
  let := hr.normal
  rw [ker_subgroupMap, QuotientGroup.ker_mk', hker]
  exact (pCore_subnormal_eq_comap 2 c.component_product.1.subnormal).symm

/-- The first isomorphism theorem for the literal residual action map. -/
def residualActionEquiv
    (hr : IsPReduced 2
      (omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)))
    (hker : centralizer (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M) : Set c.M) =
        pCore 2 c.M) :
    letI := hr.normal
    (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      (pResidual 2 c.M).map (actionMk (omegaOrbit
        (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M))) := by
  letI := hr.normal
  let f := actionMk (omegaOrbit
    (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M))
  exact (QuotientGroup.quotientMulEquivOfEq (c.residual_action_kernel hr hker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap (pResidual 2 c.M))
      (f.subgroupMap_surjective (pResidual 2 c.M)))

/-- This transport uses the original quotient map on every component element. -/
theorem residualActionEquiv_mk
    (hr : IsPReduced 2
      (omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)))
    (hker : centralizer (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M) : Set c.M) =
        pCore 2 c.M) (k : pResidual 2 c.M) :
    letI := hr.normal
    c.residualActionEquiv hr hker (QuotientGroup.mk' (pCore 2 (pResidual 2 c.M)) k) =
      (actionMk (omegaOrbit
        (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M))).subgroupMap
          (pResidual 2 c.M) k := by
  rfl

/-- The already proved Frattini-small source branch on the actual overgroup. -/
theorem sp4_block_of_quotient_frattini_small
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier)
    (hsmall : ⁅pCore 2 c.M, pResidual 2 c.M⁆ ≤
      (frattini (pCore 2 c.M)).map (pCore 2 c.M).subtype ⊔
        omegaCenterIn (pCore 2 c.M)) : ChapterC.IsSp4FourBlock (pResidual 2 c.M) := by
  exact source_tensor_sp4_block_of_frattini_small D m.sylow_not_normalizes_component
    c.M (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
    c.outside c.sylow (pResidual 2 c.M) c.component_product.1
    ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
    c.component_product.2.2.2 hsmall

/-- Actual MS consumer of the transported action marking. The identification
of its kernel and the Frattini bound remain explicit independent premises. -/
theorem sp4_block_of_action_frattini_small
    (hr : IsPReduced 2
      (omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)))
    (hker : centralizer (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M) : Set c.M) =
        pCore 2 c.M)
    (hsmall : ⁅pCore 2 c.M, pResidual 2 c.M⁆ ≤
      (frattini (pCore 2 c.M)).map (pCore 2 c.M).subtype ⊔
        omegaCenterIn (pCore 2 c.M)) :
    letI := hr.normal
    ((pResidual 2 c.M).map (actionMk (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M))) ≃*
        Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
      ChapterC.IsSp4FourBlock (pResidual 2 c.M) := by
  let := hr.normal
  intro eact
  exact c.sp4_block_of_quotient_frattini_small
    ((c.residualActionEquiv hr hker).trans eact) hsmall

end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
