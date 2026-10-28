module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt.Actions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.PlaneContradiction
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# Full-point normality when every component is an outside A₅

The actual outside-component action centralizes every component image modulo
O₂(H). If O₃(H*) is nontrivial, source 14.7.27 identifies it with the point
image. Otherwise F(H*) is trivial, so centralizing all components centralizes
F*(H*), and its self-centralization forces the point image to be trivial.
In both cases the point image is normal. Two-perfectness and the original
Sylow normalization lift this through the literal two-core quotient.

This is an intermediate with an explicit component-family hypothesis; its
producer from the original plane-centrality assumption is separate. Neither
source 14.7.47 nor normality of the point is assumed.
Source: Aschbacher–Smith 14.7.27–28,41,47, printed pp.1054–1063,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem point_star_centralizes_outside_five
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map I.subtype) :
    ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
      centralizer (C.map (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I)) := by
  have hc : ((C.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  let : C.Normal := by
    have hn := local_cComponent_normal_at d h hab structural previous faithful earlier
      I (C.map I.subtype) hI (map_subtype_le C) hc
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hn
  have hfield : Nat.card (GaloisField 2 2) = 2^2 := GaloisField.card 2 2 (by decide)
  obtain ⟨_,hfix,_⟩ := OutsideLinearTwoSourceAt.local_linearTwo_component_normalizes_point_at
    d h hab structural previous faithful earlier I hI C hout hfield (by decide)
    (eC.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm)
  let q := QuotientGroup.mk' (pCore 2 I)
  let e := cComponentTwoCoreQuotientEquiv hC
  rintro _ ⟨a,ha,rfl⟩ z hz
  obtain ⟨c,hc,rfl⟩ := hz
  let c' : C := ⟨c,hc⟩
  have he := MulEquiv.congr_fun (show normalQuotientAction C (pCore 2 C) a = 1 from hfix ha)
    (QuotientGroup.mk' (pCore 2 C) c')
  rw [normalQuotientAction_apply_mk] at he
  change QuotientGroup.mk' (pCore 2 C) (MulAut.conjNormal a c') =
    QuotientGroup.mk' (pCore 2 C) c' at he
  have hh := congrArg (fun y => (e y : HStar I)) he
  change q (a*c*a⁻¹) = q c at hh
  rw [map_mul,map_mul,map_inv] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- If every actual full-point component is an outside alternating-five
component, the original point residual is normal in the full point group. -/
theorem local_point_normal_of_all_components_outside_five_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hall : ∀ C : Subgroup F.H, C.IsCComponent →
      Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) ∧
        ¬ F.Li L 1 ≤ C.map F.H.subtype) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  let q := QuotientGroup.mk' (pCore 2 F.H)
  let A := ((F.Li L 1).subgroupOf F.H).map q
  apply WholeResidualAssembly.GuardedSource.local_point_normal_of_star_normal h structural F.H
    (sup_le (F.Li_one_le_of_mem_Hz hH) (F.sylow_le_of_mem_Hz hH))
  change A.Normal
  rcases WholeResidualAssembly.GuardedSource.local_threeCore_eq_bot_or_point
    d h hab structural previous faithful earlier F.H hH with hzero | hpoint
  · have hfit : fittingSubgroup (HStar F.H) = ⊥ :=
      (WholeResidualAssembly.GuardedSource.local_fitting_eq_threeCore
        h hab structural previous faithful F.H hH).trans hzero
    have hE : componentLayer (HStar F.H) ≤ centralizer (A : Set (HStar F.H)) := by
      apply sSup_le
      intro K hK
      let : Group.IsNilpotent (pCore 2 F.H) := pCore_isNilpotent
      obtain ⟨C,hC,he⟩ := hK.isCComponent.exists_map_quotient_eq (pCore 2 F.H)
      obtain ⟨⟨eC⟩,hout⟩ := hall C hC
      apply le_centralizer_iff.mp
      rw [←he]
      exact point_star_centralizes_outside_five d h hab structural previous faithful earlier
        F.H hH C hC eC hout
    have hAF : A ≤ centralizer (generalizedFitting (HStar F.H) : Set (HStar F.H)) := by
      apply le_centralizer_iff.mpr
      change fittingSubgroup (HStar F.H) ⊔ componentLayer (HStar F.H) ≤ _
      rw [hfit,bot_sup_eq]
      exact hE
    have hAbot : A = ⊥ := le_bot_iff.mp
      (hAF.trans (centralizer_generalizedFitting_le_fitting.trans hfit.le))
    rw [hAbot]
    infer_instance
  · change pCore 3 (HStar F.H) = A at hpoint
    rw [←hpoint]
    infer_instance

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
