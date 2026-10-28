module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.SourceImages
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalUnitaryNoncentrality.Applicability
/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalUnitaryBaumann.SourceImages`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every remaining contrary source case has the unique marked Thompson
and Baumann image. All movement and point-radical premises are discharged. -/
theorem unitary_original_offender_images_of_escape
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222At KnownSimple.IsKnownSimple D.T)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hout : ¬ normalizer (ChapterB.baumann ((D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2) : Set G) ≤
      normalizer (D.L : Set G)) :
    let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
    ∃ (rho : Automizer D.V →* Atlas.G2.Model F) (E : Additive D.V ≃ₗ[F] W),
      (∀ a v, E (automizerRepresentation D.V a v) =
        Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) ∧
      pointCoordinateSubspace E D.V₁ = pointLine ∧
      pointCoordinateSubspace E D.Vplus = seed ∧
      (inducedAutomizer D.V (D.L ⊔ (D.T : Subgroup G))).map rho = ⊤ ∧
      D.V ≤ ChapterB.baumann R ∧
      (inducedAutomizer D.V (Stellmacher.elementaryAbelianMaxJ R)).map rho =
        Atlas.G2.BinaryCore.elementary ∧
      (inducedAutomizer D.V (ChapterB.baumann R)).map rho =
        Atlas.G2.BinaryCore.elementary ∧
      D.V ⊓ centralizer (Stellmacher.elementaryAbelianMaxJ R : Set G) = D.Vplus ∧
      D.V ⊓ centralizer (ChapterB.baumann R : Set G) = D.Vplus := by
  intro R
  have hTN := (unitary_original_module_normalizers h hmax eL chosen structural).1
  have hNL := (unitary_original_module_normalizers h hmax eL chosen structural).2
  let P := D.L₁ ⊔ (D.T : Subgroup G)
  have hL1 : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  have hPX : P ≤ D.L ⊔ (D.T : Subgroup G) := sup_le_sup hL1 le_rfl
  have hPN : P ≤ normalizer (D.V : Set G) :=
    sup_le (hL1.trans chosen.normalizes) hTN
  have hJ : ¬ Stellmacher.elementaryAbelianMaxJ R ≤ centralizer (D.V : Set G) := by
    intro hcentral
    exact hout
      (unitary_baumann_normalizer_of_thompson_centralizes h chosen hmax eL hTN
        P le_sup_right hPX hcentral)
  obtain ⟨rho,E,he,_,hd,hz,_,hs⟩ := exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
    chosen.normalizes hNL e E0 he0 hTN hZV hBV hUV hTZ hTB hTU hZ hB hU
  have hTC := hTZ.trans (normalizer_le_centralizer_of_card_two D.V₁ hZ)
  have hR := unitary_original_point_radical_image D.T D.L D.V₁ rho E he hz hZV hTC
    chosen.sylow_normalizes_component chosen.normalizes hTN hd
  have hVR : D.V ≤ R := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.V)
    (chosen.le_sylow.trans le_sup_right) hPN
  have him := unitary_point_images_on_automizer rho E he R
    ((pCoreIn_le 2 P).trans hPN) hVR hR hJ
  have hJR : Stellmacher.elementaryAbelianMaxJ R ≤ R := sSup_le fun _ hA => hA.1
  have hfull : (inducedAutomizer D.V (D.L ⊔ (D.T : Subgroup G))).map rho = ⊤ := by
    have hroot : Atlas.G2.rootC (1 : F) ∈
        (inducedAutomizer D.V (Stellmacher.elementaryAbelianMaxJ R)).map rho := by
      rw [him.2.1,Atlas.G2.Natural.BinaryModelOffenders.elementary_eq]
      exact Atlas.G2.NaturalOffenders.rootC_mem_elementary 1
    have hJL := hJR.trans ((pCoreIn_le 2 P).trans hPX)
    have hJimage := map_mono (f := rho) (map_mono (f := D.V.normalizerMonoidHom.rangeRestrict)
      (subgroupOf_mono (normalizer (D.V : Set G)) hJL))
    have hLimage := map_mono (f := rho) (map_mono (f := D.V.normalizerMonoidHom.rangeRestrict)
      (subgroupOf_mono (normalizer (D.V : Set G))
        (show D.L ≤ D.L ⊔ (D.T : Subgroup G) from le_sup_left)))
    exact Atlas.G2.Natural.BinaryNormalizer.eq_top_of_derived_le (hd.trans hLimage)
      (hJimage hroot) Atlas.G2.Natural.BinaryNormalizer.rootC_not_mem_derived
  refine ⟨rho,E,he,hz,hs,hfull,him.1,him.2.1,him.2.2,?_,?_⟩
  · exact unitary_centralizer_eq_marked_seed rho E he _ D.Vplus
      (hJR.trans ((pCoreIn_le 2 P).trans hPN)) hUV hs him.2.1
  · exact unitary_centralizer_eq_marked_seed rho E he _ D.Vplus
      (inf_le_left.trans ((pCoreIn_le 2 P).trans hPN)) hUV hs him.2.2
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
