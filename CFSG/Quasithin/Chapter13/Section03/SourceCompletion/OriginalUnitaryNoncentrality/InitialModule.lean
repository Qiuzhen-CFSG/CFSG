module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.PushingUp
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.ExceptionalCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# Exceptional initial module in the original contrary unitary case

The literal L Baum(R₁) pair constructed from plane centrality satisfies the
exceptional MS hypotheses. Its radical-center orbit and whole central omega
layer both have centralizer O₂, and their moving parts under L agree. The
actual quotient action is faithful and FF. The final theorem gives the genuine
G₂ block once the exact MS93 Frattini containment is supplied.

That containment and the final page-888 normalizer argument remain with
qt-d-13316-noncentrality. The final qt-d-13316-source owner discharges only the
earlier universal source statements and independent plane-centralizer input.
Source: AS C.1.31–32, 13.3.10(2), 13.3.14; MS93 (3.2), (3.6).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]

theorem unitary_original_baumann_initial_of_plane_centrality
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
    let S := (ChapterB.baumann R).subgroupOf Y
    let K := D.L.subgroupOf Y
    centralizer (ChapterC.MSCentralOrbit.omegaOrbit S : Set Y) = pCore 2 Y ∧
      centralizer (omegaCenterIn (pCore 2 Y) : Set Y) = pCore 2 Y ∧
      ⁅ChapterC.MSCentralOrbit.omegaOrbit S,K⁆ = ⁅omegaCenterIn (pCore 2 Y),K⁆ ∧
      ∃ a : Representation F (Y ⧸ pCore 2 Y) (Additive (omegaCenterIn (pCore 2 Y))),
        Function.Injective a ∧ Representation.BinaryOffender.IsFFModule a ∧
        ∀ (y : Y) (v : Additive (omegaCenterIn (pCore 2 Y))),
          ((a (QuotientGroup.mk' (pCore 2 Y) y) v).toMul : Y) = y * v.toMul * y⁻¹ := by
  intro R Y S K
  obtain ⟨_,_,_,_,⟨d⟩,_⟩ := unitary_original_baumann_pushingUp_of_plane_centrality D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
  exact ⟨d.omegaOrbit_centralizer,d.centralOmega_centralizer,d.initialCore_eq,
    d.centralOmegaAction,d.centralOmegaAction_faithful,d.centralOmega_FF,d.centralOmegaAction_apply⟩

/-- The original component is a natural G₂ block after the remaining whole-core step. -/
theorem unitary_original_g2_block_of_frattini_small
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
    (hc : ⁅D.QH,B⁆ = ⊥)
    (hsmall : let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
      let Y := D.L ⊔ ChapterB.baumann R
      ⁅pCore 2 Y,D.L.subgroupOf Y⁆ ≤
        (frattini (pCore 2 Y)).map (pCore 2 Y).subtype ⊔ omegaCenterIn (pCore 2 Y)) :
    ChapterC.IsG2TwoBlock D.L := by
  let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
  let Y := D.L ⊔ ChapterB.baumann R
  obtain ⟨_,_,_,_,⟨d⟩,_⟩ := unitary_original_baumann_pushingUp_of_plane_centrality D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
  obtain ⟨_,hs,hm⟩ := d.block_of_frattini_small hsmall
  let eK : D.L.subgroupOf Y ≃* D.L := subgroupOfEquivOfLe le_sup_left
  exact ⟨hs.of_mulEquiv eK,hm.of_mulEquiv eK⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
