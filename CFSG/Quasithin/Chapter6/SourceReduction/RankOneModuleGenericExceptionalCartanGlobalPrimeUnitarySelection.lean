module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeRankOneSelection
public import Theory.SpecificGroups.PSU3.UniversalCover.BinaryModels

/-!
# The unitary source component and the complete single-Bender selection

The source marking identifies the component image in H/core_H(M), whereas
F.1.1 requires its intrinsic quotient by O₂. The canonical map from the
latter quotient onto the marked projective unitary group is surjective.
Quasisimplicity and trivial two-core allow the proved binary covering
calculation to recognize the original quotient as SU₃ or PSU₃, retaining
the original field parameter, including field order eight.

Together with the linear/Suzuki comparison this completes the single
Bender row of E.2.2. Its component equals the actual residual, which supplies
the full prime-pair LocalData and forces the zero-core branch with genuine
F.1.1. The model exclusions and the remaining exchanged and diagram selections
are still required for full local-to-global normalization.
Source: Aschbacher–Smith E.2.2(2a), I.1.3, 5.1.10(2) and 5.2.2,
printed pp.215–216,407,634,646–648 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open BenderSuzuki.MatrixGroups
variable {X : Type*} [Group X] [Finite X]

/-- The marked source unitary image gives an actual SU₃ or PSU₃ intrinsic quotient. -/
theorem unitary_component_quotient
    {M C : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hO : pCore 2 X ≤ sourceKernel M) (hm : UnitaryModel M C f) :
    ChapterF.Source.IsRankOneModel (C ⧸ pCore 2 C) := by
  let eC := cComponentTwoCoreQuotientEquiv hC
  let q := QuotientGroup.map (pCore 2 X) (sourceKernel M) (MonoidHom.id X) hO
  let r : actorImage C →* sourceImage M C :=
    (q.comp (actorImage C).subtype).codRestrict _ (by
      rintro ⟨x,k,hk,rfl⟩
      exact ⟨k,hk,rfl⟩)
  have hr : Function.Surjective r := by
    rintro ⟨x,k,hk,rfl⟩
    exact ⟨⟨QuotientGroup.mk' (pCore 2 X) k,k,hk,rfl⟩,rfl⟩
  obtain ⟨F,_,_,_,J,_,hf,hcard,hconj,_,e,_⟩ := hm
  let := hqs
  let v := (e.toMonoidHom.comp r).comp eC.toMonoidHom
  have hv : Function.Surjective v := e.surjective.comp (hr.comp eC.surjective)
  rcases HermitianForm.UniversalCover.binary_cover_models J hf hcard hconj v hv
      (pCore_quotient_pCore_eq_bot (p := 2) (G := C)) with hj | hj
  · exact .projective_unitary f (by omega)
      ⟨F,inferInstance,inferInstance,J,hcard,hconj,hj⟩
  · exact .special_unitary f (by omega)
      ⟨F,inferInstance,inferInstance,J,hcard,hconj,hj⟩

/-- Every single-Bender source row has the required intrinsic rank-one quotient. -/
theorem single_bender_component_quotient
    {M C U : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hO : pCore 2 X ≤ sourceKernel M)
    (hc : SingleClauses M C U) (hm : BenderModel M C f) :
    ChapterF.Source.IsRankOneModel (C ⧸ pCore 2 C) := by
  rcases hm with hm | hm
  · exact single_linear_suzuki_component_quotient hC hqs hO hc hm
  · exact unitary_component_quotient hC hqs hO hm

variable {G : Type*} [Group G] [Finite G]

/-- The complete single-Bender source branch constructs the residual prime pair and its zero-core amalgam. -/
theorem single_bender_prime_pair
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : BenderModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    LocalData T L H B D (residual H) ∧
      (generated L H D (residual H)).pCoreIn 2 = ⊥ ∧
      ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,residual H]
        (Global.sourceS L H) := by
  have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) := by
    apply Subgroup.normal_le_normalCore.mpr
    exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans
      (comap_mono h.sylow_normalizes)
  have hr := single_bender_component_quotient hC hqs hO hc hm
  have he : C = pResidual 2 H :=
    BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc hC
  subst C
  exact rankOne_residual_prime_pair h hH c hd hr hqs

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
