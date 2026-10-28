module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.PointRanks
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.CatalogueReduction
public import CFSG.Quasithin.ChapterG.Section11.NontrivialActorCatalogue
public import Theory.Representation.BinaryPermutation.PointStabilizerRank
public import Theory.Representation.BinaryNaturalDual.Transport

/-!
# Two remaining catalogue exclusions on the original HS flag

The nontrivial conjugate-center actor excludes the natural A₇ row. In the
split six-space row, the literal normal A₈ centralizes Z(U); its point
stabilizer has three-rank at least two, contradicting the original rank-one
bound in the image of C_H(Z(U)). Both arguments retain the original flag
and its actual quotient action.

The final consumer reduces the earlier marked result to rows (2) and (6),
or the unresolved whole-component recognition branch. Centerlessness is
still the preceding premise owned by the local-structure assembly task.
The four-dimensional action identification, G₂(2) exclusion and whole-component
recognition remain necessary before constructing natural coordinates and
ActionStructure. This module does not assert an exhaustive classifier.

Source: Aschbacher--Smith, 12.8.13(6--8), G.11.2(4--5), and 14.3.24,32,
printed pp.855--857,364,1000,1003--1004.
-/

public section
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
include d earlier hq chosen structural alternatives hne hZ

/-- The nonextraspecial original HS flag excludes the natural A₇ row. -/
theorem source_no_caseFour : ¬ CaseFour F.terminalRepresentation := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨heU,heX,B,v,hyp,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  exact not_caseFour_of_smaller_ne_bot hyp
    (map_mono (comap_mono (F.conjugate_ZU_le_X g)))
    (source_earlier_conjugate_center_ne_bot d earlier hq chosen structural alternatives F hne hZ g hgP hgH)

/-- The split six-space row contradicts the actual center-centralizer
point rank, retaining centerlessness as the preceding source premise. -/
theorem source_no_caseFive (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) :
    ¬ CaseFive F.terminalRepresentation B := by
  intro h5
  obtain ⟨q,c,K,hKn,hKc,e,he⟩ := SplitSix.caseFive_selfcentralizing_marking h5
  let := hKn
  let : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 8))
  let : IsSimpleGroup K := e.isSimpleGroup
  have hKa : ¬ IsMulCommutative K := by
    intro hc
    let := hc
    let : Group.IsPerfect (alternatingGroup (Fin 8)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 8))
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  have hKC := source_simple_normal_le_center_centralizer d earlier hq chosen structural alternatives
    F hne hZ hI g hgP hgH K hKa hKc
  obtain ⟨heU,heX,B',v,hyp,hline,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hr : 2 ≤ primeRank 3 (C.subgroupOf K) := by
    let a := BinaryNaturalDual.Transport.stabilizerEquiv (F.terminalRepresentation.comp K.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e c.toLinearEquiv he v
    have hb := BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) (c v)
    exact hb.trans (primeRank_equiv 3 a).ge
  let f : C.subgroupOf K →* C.subgroupOf D := {
    toFun := fun a => ⟨⟨a.val.val,hKC a.val.property⟩,a.property⟩
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

section
omit d earlier hq chosen structural alternatives hne hZ
omit [IsElementaryAbelian 2 F.Uhat]
open ChapterG.Section11.ExchangedRecognition
/-- Apply the literal catalogue sieve to the original HS flag, retaining the
whole-component recognition obligation with all its original hypotheses. -/
theorem source_remaining_action_of_centerless (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ((CaseTwo F.terminalRepresentation B ∨ CaseSix F.terminalRepresentation) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
            WholeComponentCandidates.Alternatives F.terminalRepresentation J
              (componentOrbit J ⊤))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hcases⟩ :=
    source_earlier_remaining_action d earlier hq chosen structural alternatives F hne hZ g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases hcases with h2 | hwhole
  · left
    rcases h2 with h2 | h4 | h5 | h6
    · exact .inl h2
    · exact (source_no_caseFour d earlier hq chosen structural alternatives F hne hZ h4).elim
    · exact (source_no_caseFive d earlier hq chosen structural alternatives F hne hZ hI B h5).elim
    · exact .inr h6
  · exact .inr hwhole
end
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
