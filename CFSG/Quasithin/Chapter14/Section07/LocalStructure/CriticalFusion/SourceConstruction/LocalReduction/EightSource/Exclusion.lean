module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.Exclusion.Marking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.KernelCover
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.NonEnlargement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.Marked

/-!
# The original linear-four exclusion in 14.7.51

Non-enlargement identifies the local with the full point normalizer. The
actual maximal quotient and reciprocal offender give two compatible module
models; the original fixed flag removes the central kernel layer. A natural
kernel splits by the transposition rank-two bound, and an augmentation
kernel admits an equivariant retraction. Each resulting whole-module model
contradicts the original Sylow-fixed cyclic flag.

All module markings, quotient choices, kernel movement, extension splittings
and Sylow placements are constructed from the original source hypotheses.
Source: Aschbacher–Smith 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
open OffenderModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem full_point_four_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : False := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨hU,hr⟩ := full_point_four_transvection_configuration_at d h hab structural
    previous faithful earlier source47 C hC e
  let := hU
  obtain ⟨a,N,eH,c,hN,_,_,_,_,_,⟨m⟩⟩ := hr
  have hmodel := local_transvection_kernel_naturalOrCover_at d h hab structural previous
    faithful earlier source47 F.H hH C hC a N hN.ne_top eH (star F c.Uα) m
  obtain ⟨eQ,heQ⟩ := m.quotient_natural
  rcases hmodel with ⟨eN,heN⟩ | ⟨eN,heN⟩
  · let s := eH.symm (Equiv.swap 0 1)
    have hs : eH s = Equiv.swap 0 1 := eH.apply_symm_apply _
    have hA : zpowers s = star F c.Uα := by
      apply Subgroup.map_injective (f := eH.toMonoidHom) eH.injective
      rw [MonoidHom.map_zpowers]
      change zpowers (eH s) = (star F c.Uα).map eH.toMonoidHom
      rw [hs,Subgroup.zpowers_eq_closure,m.actor_marking]
    have hsmall : Module.finrank (ZMod 2) (a.representation s - LinearMap.id).range ≤ 2 := by
      rw [←fixedCodim_zpowers_eq_displacement_rank,hA,m.ambient_fixedCodim]
    obtain ⟨E,hE⟩ := SelfExtension.natural_pair_equiv a.representation N eH
      eN eQ heN heQ s ⟨0,1,by decide,hs⟩ hsmall
    exact local_double_natural_impossible_of_marking_at h hH a eH E hE
  · obtain ⟨p,hp,hpe⟩ := SelfExtension.core_surjective_retraction a.representation N eH
      eN eQ heN heQ
    exact local_core_quotient_impossible_of_marking_at h hH a eH p hp hpe

/-- The original degree-four component row is impossible. The theorem keeps
only the original local hypotheses and requires no selected module, model,
kernel-fixation or extension-splitting callback. -/
theorem source_14_7_51_linear_four_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  rintro ⟨e⟩
  have hIF := local_four_eq_full_point_at d h hab structural previous faithful earlier
    source47 I hI C hC e
  subst I
  exact full_point_four_impossible_at d h hab structural previous faithful earlier source47 C hC e

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
