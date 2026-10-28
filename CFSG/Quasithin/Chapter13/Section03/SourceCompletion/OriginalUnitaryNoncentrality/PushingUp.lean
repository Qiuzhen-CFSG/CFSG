module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.Product
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.Characteristic
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.LocalStructure
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.OffenderImages

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.ExceptionalInput

/-!
# The exceptional MS input in the original contrary unitary case

The original flag and plane-centrality assumption give the proved offender
images and Baumann escape. These construct the actual exceptional MS pair
inside Y = L Baum(O₂(L₁T)): SQTK, F*(Y) = O₂(Y), the relative C-component,
its two-residual identity, MS3, and a genuine G₂(2) quotient identifying the
Baumann subgroup with the marked normal root eight. The same quotient map
agrees with the original action and flag coordinates. The product core's
normalizer is also contained in N_G(L).

This supplies MS2(b), whereas MarkedMS.SmallMSPair and its existing G₂
reconstruction require MS2(a). The exceptional reconstruction must be proved
before using the block alternative. The final Baumann bound and noncentrality
assembly remain with qt-d-13316-noncentrality; qt-d-13316-source discharges the
earlier universal statements and independent plane-centralizer premise.
Source: Aschbacher–Smith C.1.31–37, pp.135–143; 13.3.10(2), pp.887–888,
and 13.3.14, pp.891–893.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]
theorem unitary_original_baumann_pushingUp_of_plane_centrality
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
    (hc : ⁅D.QH,B⁆ = ⊥) :
    let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
    let Y := D.L ⊔ ChapterB.baumann R
    IsSQTK KnownSimple.IsKnownSimple Y ∧
      generalizedFitting Y = pCore 2 Y ∧
      (D.L.subgroupOf Y).IsCComponent ∧
      pResidual 2 Y = D.L.subgroupOf Y ∧
      Nonempty (ChapterC.G2Exceptional.Input KnownSimple.IsKnownSimple
        (D.L.subgroupOf Y) ((ChapterB.baumann R).subgroupOf Y)) ∧
      normalizer (Y.pCoreIn 2 : Set G) ≤ normalizer (D.L : Set G) ∧
      ChapterC.MSCharacteristicCondition ((ChapterB.baumann R).subgroupOf Y) ∧
      ∃ (rho : Automizer D.V →* Atlas.G2.Model F) (E : Additive D.V ≃ₗ[F] W)
        (eq : (Y ⧸ pCore 2 Y) ≃* Atlas.G2.Model F)
        (hn : Y ≤ normalizer (D.V : Set G)),
        (∀ a v, E (automizerRepresentation D.V a v) =
          Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) ∧
        pointCoordinateSubspace E D.V₁ = pointLine ∧
        pointCoordinateSubspace E D.Vplus = seed ∧
        (∀ y : Y, eq (QuotientGroup.mk' (pCore 2 Y) y) =
          rho (D.V.normalizerMonoidHom.rangeRestrict ⟨y,hn y.property⟩)) ∧
        (ChapterB.baumann R).subgroupOf Y = Atlas.G2.BinaryCore.elementary.comap
          (eq.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y))) := by
  intro R Y
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived := Atlas.G2.isSimple_commutator_binary
  obtain ⟨rho,E,he,hz,hu,hfull,hVB,hJ,hBimage,_,_⟩ :=
    unitary_original_offender_images_of_plane_centrality D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
  have hTN := (unitary_original_module_normalizers h hmax eL chosen structural).1
  let P := D.L₁ ⊔ (D.T : Subgroup G)
  let X := D.L ⊔ (D.T : Subgroup G)
  have hPX : P ≤ X := sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl
  have hRT : R ≤ (D.T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (D.T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (D.T : Subgroup G) ≤ P from le_sup_right)] using hh
  have hTR : (D.T : Subgroup G) ≤ normalizer (R : Set G) :=
    le_sup_right.trans (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  have hQ : X.pCoreIn 2 = (D.T : Subgroup G) ⊓ centralizer (D.V : Set G) :=
    (unitary_chosen_sylow_kernel chosen eL.isSimpleGroup hTN).symm
  have hQR : X.pCoreIn 2 ≤ R := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X)
      ((hQ.le.trans inf_le_left).trans le_sup_right)
    exact hPX.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hout := unitary_original_baumann_escape D h chosen hmax eL structural e E0 he0
    hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
  have hQnormal := unitary_baumann_core_normalizer h chosen hmax eL hTN R hRT hTR hVB
  have hm := unitary_baumann_product_characteristic h chosen hmax eL R hRT hTR hout
  have hs := unitary_baumann_product_local h chosen hmax hTN R hRT hTR
  obtain ⟨eq,heq,hpre⟩ := unitary_baumann_product_model chosen eL.isSimpleGroup
    (Chapter1.Section02.Adequate.mem_L_isPPerfect hmax.1) hTN rho E he hfull R hRT hTR hQR hJ hBimage
  have hinput : Nonempty (ChapterC.G2Exceptional.Input KnownSimple.IsKnownSimple
      (D.L.subgroupOf Y) ((ChapterB.baumann R).subgroupOf Y)) := by
    let K := D.L.subgroupOf Y
    let S := (ChapterB.baumann R).subgroupOf Y
    let : K.Normal := by
      change (D.L.subgroupOf Y).Normal
      rw [←hs.2.2.2]
      infer_instance
    refine ⟨{
      sqtk := hs.1
      fitting := hs.2.1
      component := hs.2.2.1
      product := ?_
      componentQuotient := (QuotientGroup.congr _ _
        (subgroupOfEquivOfLe (show D.L ≤ Y from le_sup_left))
        (pCore_map_iso 2 (subgroupOfEquivOfLe (show D.L ≤ Y from le_sup_left)))).trans eL
      quotient := eq
      radical := hpre
      characteristic := hm }⟩
    intro y
    have hy : y ∈ K ⊔ S := by
      change y ∈ D.L.subgroupOf Y ⊔ (ChapterB.baumann R).subgroupOf Y
      rw [←subgroupOf_sup (show D.L ≤ Y from le_sup_left)
        (show ChapterB.baumann R ≤ Y from le_sup_right),subgroupOf_self]
      trivial
    exact mem_sup_of_normal_left.mp hy
  exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hinput,hQnormal,hm, rho,E,eq,
    sup_le chosen.normalizes (inf_le_left.trans (hRT.trans hTN)),he,hz,hu,heq,hpre⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
