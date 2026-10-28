module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.FourCoordinates
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeModels
public import CFSG.Quasithin.ChapterG.Section11.LargeWholePair
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeSeven
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeBinaryG2
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.SelfDual
public import Theory.Representation.BinaryPermutation.EightCentralizer

/-!
# Completing the original HS whole-component branch

The original actor satisfies the half-degree bound. The general G.9
recognition excludes tensor pairs and all single-component carriers except
A7, A8 and binary G2 derived, preserving the actual centers and actions.
The nontrivial conjugate-center actor excludes A7. The A8 deleted action
has point-centralizer three-rank two, contradicting the original rank-one
bound inside the image of C_H(Z(U)). The binary G2 derived component
recognizes the full natural G2(2) action, already excluded on this flag.

Consequently the checked four-dimensional branch supplies ActionStructure
without any remaining module-recognition premise. Its literal LocalStructure
consumer is included. Centerlessness is the preceding independent premise,
whose final discharge remains with qt-d-hs-local-structure.
Source: Aschbacher--Smith 14.3.23--24 and 14.3.32, printed pp.999--1004.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
include d earlier hq chosen structural alternatives hne hZ hI

/-- The whole A8 component contradicts the original center-centralizing point rank. -/
theorem source_no_whole_alternating_eight
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (J : Subgroup F.TerminalHdot)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) J J
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (e₀ : J ≃* alternatingGroup (Fin 8)) : False := by
  let := h9.normal_H
  obtain ⟨e,c,hc⟩ :=
    ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternating_natural_of_selfDual
      h9 (LargeWhole.selfDual hyp)
      (e₀.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  have hJc := BinaryPermutation.EightCommutant.centralizer_eq_bot_of_coordinates
    F.terminalRepresentation hyp.faithful J e c hc
  let : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 8))
  let : IsSimpleGroup J := e.isSimpleGroup
  have hJa : ¬ IsMulCommutative J := fun hh =>
    h9.component.isCComponent.not_isSolvable (by let := hh; infer_instance)
  have hJC := source_simple_normal_le_center_centralizer d earlier hq chosen structural alternatives
    F hne hZ hI g hgP hgH J hJa hJc
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hr : 2 ≤ primeRank 3 (C.subgroupOf J) := by
    let a := BinaryNaturalDual.Transport.stabilizerEquiv (F.terminalRepresentation.comp J.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e c hc v
    have hb := BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) (c v)
    exact hb.trans (primeRank_equiv 3 a).ge
  let f : C.subgroupOf J →* C.subgroupOf D := {
    toFun := fun a => ⟨⟨a.val.val,hJC a.val.property⟩,a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C.subgroupOf D => z.val.val) he))
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  have hu := source_center_centralizing_point_image_three_rank_le_one d earlier hq chosen
    structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (C.subgroupOf D) ≤ 1 at hu
  omega

/-- Every whole-component action above dimension four is excluded on the
original HS flag, using precisely its low-rank, relative Sylow and half-degree inputs. -/
theorem source_no_whole_component
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hw : LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat))
    (J : Subgroup F.TerminalHdot)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) : False := by
  have hlarge := source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
    F g hne hZ hgP hgH
  by_cases he : componentOrbit J ⊤ = J
  · rw [he] at h9
    obtain ⟨_,hc⟩ := LargeWhole.single_small_carrier hyp h9 hw hS hd hlarge
    cases hc with
    | seven e =>
      exact LargeWhole.not_seven_of_smaller_ne_bot hyp h9 hd
        (map_mono (comap_mono (F.conjugate_ZU_le_X g)))
        (source_earlier_conjugate_center_ne_bot d earlier hq chosen structural alternatives
          F hne hZ g hgP hgH) e.some
    | eight e =>
      exact source_no_whole_alternating_eight d earlier hq chosen structural alternatives
        F hne hZ hI g hgP hgH B v hyp hline J h9 e.some
    | binary_g2 e =>
      exact source_no_caseSix d earlier hq chosen structural alternatives F hne hZ hI
        (LargeWhole.caseSix_of_binary_g2 hyp h9 hd hlarge e.some)
  · exact LargeWhole.not_component_pair hyp hw hlarge h9 he

omit [IsElementaryAbelian 2 F.Uhat] in
/-- The complete original ActionStructure contract, conditional only on the
preceding centerlessness statement and the authorized earlier-source inputs. -/
theorem source_actionStructure_of_centerless : ActionStructure F := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  rcases source_action_or_whole_recognition_of_centerless d earlier hq chosen structural alternatives
      F hne hZ hI g hgP hgH with ha | ⟨heU,heX,B,v,hyp,hline,hw,hS,_,hd,_,J,_,_,_,h9,_⟩
  · exact ha
  · let := heU
    let := heX
    exact (source_no_whole_component d earlier hq chosen structural alternatives
      F hne hZ hI g hgP hgH B v hyp hline hw hS hd J h9).elim

omit [IsElementaryAbelian 2 F.Uhat] in
/-- Apply the proved unrestricted action to the original LocalStructure
consumer. Centerlessness is discharged by its independent source owner. -/
theorem source_localStructure_of_centerless : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne hI
    (source_actionStructure_of_centerless d earlier hq chosen structural alternatives F hne hZ hI)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
