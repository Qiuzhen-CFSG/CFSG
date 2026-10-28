module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Quotients
public import Theory.Representation.BinaryAlternatingSevenControl.NormalExtension

/-!
# The marked ambient quotient in the rank-four branch of 14.7.50

The faithful A₇ image in a binary four-space is self-normalizing. Thus
all operators of a normal extension already belong to that image. The
proper-quotient faithfulness proved from the original local hypotheses
then forces the ambient quotient to equal its A₇ component. Composing
with the original seven-letter marking gives an actual A₇ isomorphism,
compatible with the supplied marking of C/O₂(C).

This proves the source sentence that H* is A₇ in the rank-four case.
The partition-stabilizer placement and inverter contradiction remain
necessary to exclude that case.

Source: Aschbacher–Smith 14.7.50, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem normal_seven_eq_top_of_faithful_four
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) X W) (hσ : Function.Injective σ)
    (B : Subgroup X) [B.Normal] (e : B ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) W = 4) : B = ⊤ := by
  let τ := (σ.comp B.subtype).comp e.symm.toMonoidHom
  have hτ : Function.Injective τ := hσ.comp (B.subtype_injective.comp e.symm.injective)
  have he : ∀ b : B, σ b = τ (e b) := by
    intro b
    change σ b.val = σ (e.symm (e b)).val
    rw [e.symm_apply_apply]
  apply top_unique
  intro x _
  obtain ⟨a,ha⟩ := BinaryAlternatingSevenControl.exists_operator_of_normal_extension
    σ B τ hτ hd e.toMonoidHom e.surjective he x
  have hx : x = (e.symm a).val := hσ ha
  rw [hx]
  exact (e.symm a).property

/-- The rank-four branch of 14.7.50 has the marked whole quotient A₇.
Faithfulness of the proper quotient is proved from the original local
hypotheses, and self-normalization of the A₇ four-space eliminates S₇. -/
theorem local_four_quotient_alternating_marking_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (hd : Module.finrank (ZMod 2)
      (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I)) ⧸ N.toSubmodule) = 4) :
    ∃ b : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7),
      ∀ c : C, b (QuotientGroup.mk' (pCore 2 I) c.val) =
        e (QuotientGroup.mk' (pCore 2 C) c) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  have hr := (local_component_eq_residual_at d h hab structural previous faithful earlier
    source47 I hI C hC).1
  let : C.Normal := hr ▸ inferInstance
  let : B.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  let eB : B ≃* alternatingGroup (Fin 7) :=
    (cComponentTwoCoreQuotientEquiv hC).symm.trans e
  have hB : B = ⊤ := normal_seven_eq_top_of_faithful_four N.quotientRepresentation
    (local_proper_quotient_faithful_at d h hab structural previous faithful earlier
      source47 I hI C hC a N hN) B eB hd
  obtain ⟨j,hj,hmark,hm,_⟩ := local_permutation_marking_at d h hab structural previous
    faithful earlier source47 I hI C hC e
  have him : j.range = alternatingGroup (Fin 7) := by
    have he : B.map j = alternatingGroup (Fin 7) := by
      rw [Subgroup.map_map]
      exact hm
    rwa [hB,←MonoidHom.range_eq_map] at he
  refine ⟨(MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr him),?_⟩
  intro c
  exact Subtype.ext (hmark c)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
