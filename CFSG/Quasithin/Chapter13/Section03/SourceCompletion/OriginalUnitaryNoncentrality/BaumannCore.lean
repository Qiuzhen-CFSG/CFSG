module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.CoreContainment
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.OffenderImages
/-!
# Baumann core containment in the original contrary unitary case

The original plane-centrality assumption supplies the marked offender
images through the proved normalizer escape. The literal point radical
R₁=O₂(L₁T) contains O₂(LT), and T normalizes it. The full-action Baumann
argument consequently proves O₂(L Baum(R₁)) ≤ Baum(R₁) and identifies it
with C_Baum(R₁)(V). No core-containment premise is added.

The remaining characteristic-subgroup/block and normalizer arguments stay
with qt-d-13316-noncentrality; the earlier universal source statements and
plane-centralizer premise are discharged by qt-d-13316-source.
Source: Aschbacher–Smith13.3.10(2), p.888, in13.3.14, pp.891–893.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]
theorem unitary_original_baumann_core_of_plane_centrality
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
    (D.L ⊔ ChapterB.baumann R).pCoreIn 2 ≤ ChapterB.baumann R ∧
      (D.L ⊔ ChapterB.baumann R).pCoreIn 2 =
        ChapterB.baumann R ⊓ centralizer (D.V : Set G) := by
  intro R
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived := Atlas.G2.isSimple_commutator_binary
  obtain ⟨rho,E,he,_,_,hfull,_,hJ,_,_,_⟩ :=
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
  exact unitary_baumann_core_of_point_image chosen eL.isSimpleGroup
    (Chapter1.Section02.Adequate.mem_L_isPPerfect hmax.1) hTN rho E he hfull R hRT hTR hQR hJ

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
