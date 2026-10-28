module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.At.Geometry
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.RankOneReduction
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.RankOneExclusion
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ClassicalExclusion
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SingleComponentReduction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.AlternatingEightExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.PointStabilizer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Geometry
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Actor
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FullActions
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Assembly
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.LocalAction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Recognition
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Partner
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Recognition
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.MathieuComponentExclusion
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineModule
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SingleComponentFixedLine
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SmallComponentReduction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ComponentOrbitRecognition

/-!
# The component and Mathieu reductions at G,T

Apply the existing intrinsic G.9 and G.11 results to the original terminal
action. Actual component orbits, point stabilizers and local actions retain
their quotient maps. The marked Mathieu partner produces the three-vertex
system, and its PSL4(2) recognition contradicts the original Sylow order.

The earlier inputs are restricted to the original group and Sylow subgroup.
The universal APIs remain unchanged. The `import all` edges intentionally
reuse the private calculations of the corresponding source implementation;
only deductions depending on the earlier inputs are specialized here.
Source: Aschbacher--Smith, 14.4.2,8,12--13; printed pp.1006--1007,1009,1011--1012; refs/quasithin.pdf.
-/

public noncomputable section

/- Specialization of CaseOneLarge/RankOneReduction.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Theory.GroupTheory

open scoped IsMulCommutative MatrixGroups TensorProduct


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_large_bender_component_triple_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C, F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (model : ClassificationModels.IsBenderModel C) :
    RankOne.TripleModel F.terminalRepresentation (F.terminalDot (F.X g)) C := by
  obtain ⟨_,_,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
    have hcenter := (source_extraspecial_order_at d earlier hq chosen structural alternatives
      F hne hZ).1.center_order_p
    have hc : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
      rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hcenter]
      change Nat.card (Additive F.Uhat) * 2 = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,pow_succ]
    by_contra hn
    have hb := Nat.pow_le_pow_right (n := 2) (by decide)
      (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 6)
    rw [← hc] at hb
    norm_num at hb
    omega
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  apply RankOne.triple_of_bender hyp h9 ?_ hd model
  rcases source_terminal_fixed_point_alternative_at d earlier hq chosen structural alternatives
      F hne g hgP hgH v hline with hf | ⟨a,_,hr,hv⟩
  · exact Or.inl hf
  · exact Or.inr ⟨a,a.property,hr,hv⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/RankOneExclusion.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative MatrixGroups TensorProduct


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_no_triple_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (C : Subgroup F.TerminalHdot) [C.Normal]
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : C ≃* SL(2,k)) (hk : Nat.card k = 8)
    (ht : letI : Algebra (ZMod 2) k := SL2.BinarySmall.binaryAlgebra
      SL2.BinarySmall.IsTriple ((F.terminalRepresentation.comp C.subtype).comp e.symm.toMonoidHom)) :
    False := by
  let := chosen.elementary
  let := hirr
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,_,B,v,hyp,hline,hfix⟩ := source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  have hP : (P : Subgroup F.TerminalHdot) = F.terminalDot (T : Subgroup G) := rfl
  have hs : (P : Subgroup F.TerminalHdot) ≤ subspaceStabilizer F.terminalRepresentation (hatSpace F V) := by
    apply le_subspaceStabilizer
    intro a ha w hw
    obtain ⟨b,hb,rfl⟩ := (show a ∈ F.terminalDot (T : Subgroup G) from hP ▸ ha)
    apply rankOne_seed_stable F b _ w hw
    have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := by
      simpa only [F.last] using F.invariant 3
    exact hTV hb
  obtain ⟨a,ha,hm⟩ := CaseOneHS.source_seed_point_moved_at d earlier hq chosen F hne v hline
  apply hm
  apply RankOne.triple_seed_point_fixed F.terminalRepresentation C e hk ht P (hatSpace F V)
    (seed_hat_dimension F (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2)
    hs v hyp.point_ne_zero (fun b => hfix b (hP ▸ b.property)) a
  have hstable : F.terminalDot (F.Li L 1) ≤ subspaceStabilizer F.terminalRepresentation (hatSpace F V) := by
    apply le_subspaceStabilizer
    intro b hb w hw
    obtain ⟨c,hc,rfl⟩ := hb
    exact rankOne_seed_stable F c (chosen.normalizes (F.Li_le L 1 hc).1) w hw
  exact hstable ha

theorem source_large_no_bender_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (model : ClassificationModels.IsBenderModel C) : False := by
  obtain ⟨_,_,k,_,_,_,e,hk,ht⟩ := source_large_bender_component_triple_at d earlier hq chosen
    structural alternatives F hne hZ hlarge g hgP hgH C hC hm hirr model
  exact source_no_triple_component_at d earlier hq chosen structural alternatives F hne C hirr e hk ht

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/ClassicalExclusion.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative MatrixGroups


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_no_nonbinary_symplectic_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSp C 2 (2^n)) : False := by
  obtain ⟨_,_,B,v,hyp,_,hfix⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v
      (F.terminalDot (F.X g)) :=
    ⟨_,hfix,source_terminal_actor_normal_in_sylow_at d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  exact ClassicalComponents.not_nonbinary_symplectic hyp hS h9 hn model

theorem source_no_nonbinary_g2_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    {n : ℕ} (hn : 2 ≤ n) (model : ClassificationModels.IsG2At C (2^n)) : False := by
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact ClassicalComponents.not_nonbinary_g2 hyp h9 e hn hcard

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/SingleComponentReduction.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative MatrixGroups


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_large_single_component_reduction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) :
    (IsSimpleGroup C ∧ (ChapterG.Section11.LargeWhole.SmallCarrier C ∨
      (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
        Nonempty (C ≃* Sporadic.Mathieu.M22)))) ∨
    (Chapter1.Section02.LocalModels.IsM22Cover C ∧ finrank (ZMod 2) (Additive F.Uhat) = 12) := by
  obtain ⟨_,_,B,v,hyp,hline,hfix⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v
      (F.terminalDot (F.X g)) :=
    ⟨_,hfix,source_terminal_actor_normal_in_sylow_at d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
  have hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
    have hcenter := (source_extraspecial_order_at d earlier hq chosen structural alternatives
      F hne hZ).1.center_order_p
    have hc : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
      rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hcenter]
      change Nat.card (Additive F.Uhat) * 2 = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,pow_succ]
    by_contra hn
    have hb := Nat.pow_le_pow_right (n := 2) (by decide)
      (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 6)
    rw [← hc] at hb
    norm_num at hb
    omega
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  have halt : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} ∨
      ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
    rcases source_terminal_fixed_point_alternative_at d earlier hq chosen structural alternatives
        F hne g hgP hgH v hline with hf | ⟨a,_,hr,hv⟩
    · exact .inl hf
    · exact .inr ⟨a,a.property,hr,hv⟩
  have hb := source_large_no_bender_component_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH C hC hm hirr
  have hs := fun n hn => source_no_nonbinary_symplectic_component_at d earlier hq chosen structural
    alternatives F hne g hgP hgH C hC hm hirr (n := n) hn
  have hg := fun n hn => source_no_nonbinary_g2_component_at d earlier hq chosen structural
    alternatives F hne g hgP hgH C hC hm hirr (n := n) hn
  rcases SingleComponent.remaining hyp h9 hS hd halt hb hs hg with
    ⟨hi,hsmall | ⟨hf,_,hmodel⟩⟩ | hc
  · exact .inl ⟨hi,.inl hsmall⟩
  · exact .inl ⟨hi,.inr ⟨hf.trans hline,hmodel⟩⟩
  · exact .inr hc

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/AlternatingEightExclusion.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_no_alternating_eight_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (e₀ : C ≃* alternatingGroup (Fin 8)) : False := by
  obtain ⟨_,_,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  obtain ⟨e,c,hc⟩ :=
    ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternating_natural_of_selfDual
      h9 (ChapterG.Section11.LargeWhole.selfDual hyp)
      (e₀.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  let P := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hHc : F.H ≤ centralizer (F.ZU : Set G) := by
    rw [hZ]
    exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hD : D = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact mem_map_of_mem _ (hHc b.property)
  have hu := CaseOneHS.source_center_centralizing_point_image_three_rank_le_one_at
    d earlier hq chosen structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (P.subgroupOf D) ≤ 1 at hu
  have hpD : P ≤ D := by rw [hD]; exact le_top
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe hpD)] at hu
  have hr : 2 ≤ primeRank 3 (P.subgroupOf C) := by
    let a := BinaryNaturalDual.Transport.stabilizerEquiv (F.terminalRepresentation.comp C.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e c hc v
    have hb := BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) (c v)
    exact hb.trans (primeRank_equiv 3 a).ge
  let j : P.subgroupOf C →* P := {
    toFun a := ⟨a.val.val,a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : P => z.val) he))
  have hh := Theory.GroupTheory.primeRank_le_of_injective 3 j hj
  omega

theorem source_large_single_component_models_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) :
    (IsSimpleGroup C ∧
      (Nonempty (C ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
        (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
          Nonempty (C ≃* Sporadic.Mathieu.M22)))) ∨
    (Chapter1.Section02.LocalModels.IsM22Cover C ∧ finrank (ZMod 2) (Additive F.Uhat) = 12) := by
  rcases source_large_single_component_reduction_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH C hC hm hirr with ⟨hi,hsmall | hfixed⟩ | hcover
  · refine .inl ⟨hi,?_⟩
    cases hsmall with
    | seven he => exact .inl he
    | eight he => exact (source_no_alternating_eight_component_at d earlier hq chosen structural
        alternatives F hne hZ g hgP hgH C hC hm hirr he.some).elim
    | binary_g2 he => exact .inr (.inl he)
  · exact .inl ⟨hi,.inr (.inr hfixed)⟩
  · exact .inr hcover

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/PointStabilizer.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_actor_normal_in_point_stabilizer_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    F.terminalDot (F.X g) ≤ ChapterG.Section10.pointCentralizer F.terminalRepresentation v ∧
      ((F.terminalDot (F.X g)).subgroupOf
        (ChapterG.Section10.pointCentralizer F.terminalRepresentation v)).Normal := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hindex, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  obtain ⟨z,hz,hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hn := actors_normal_in_dot_H2 F (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex) g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
    F.terminalHatAction F.terminalHatAction_apply_mk
  rw [source_point_stabilizer F hZ v hv hline]
  exact ⟨hn.1,hn.2.1⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Mathieu/Geometry.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Mathieu LargerDimension.LocalAction.Components

open LargerDimension.Mathieu.ModuleGeometry.Native hiding Group

universe u

variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem mathieu_hyperplane_of_index
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w))
    (hS : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map
      (ActorCatalogue.starProjection F.H e) = markedSylow.toSubgroup)
    (hindex : F.W.relIndex F.U = 2) :
    (mathieuCentralAction F e c he).image F.W = markedPerp := by
  let ca := mathieuCentralAction F e c he
  have hTU : (T : Subgroup G) ≤ normalizer (F.U : Set G) :=
    (F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H)
  have hTW : (T : Subgroup G) ≤ normalizer (F.W : Set G) :=
    (le_inf hTU ((F.invariant 2).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hUT : ⁅F.U,(T : Subgroup G)⁆ ≤ F.W :=
    commutator_le_of_normalized_index_two _ _ _ inf_le_left hindex hTU hTW
  have hU : ca.image F.U = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨w,rfl⟩ := c.surjective v
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (center F.U) w.toMul
    exact ⟨w,⟨a,a.property,ha⟩,rfl⟩
  have hm : subspaceCommutator ActorCatalogue.Native.action ⊤ markedSylow.toSubgroup ≤
      ca.image F.W := by
    have hh := ca.image_mono hUT
    rw [ca.image_commutator _ _ le_rfl (F.invariant 1),hU] at hh
    have ht : ((T : Subgroup G).subgroupOf F.H).map
        (ActorCatalogue.starProjection F.H e) = markedSylow.toSubgroup := hS
    rwa [ht] at hh
  apply mathieu_markedPerp_eq_of_le _ (mathieu_markedPerp_le_sylow_moved.trans hm)
  intro htop
  have hcenter : center F.U ≤ F.W.subgroupOf F.U := by
    intro z hz
    exact F.ZU_le_W (show (z:G) ∈ F.ZU from ⟨z,hz,rfl⟩)
  have hUW : F.U ≤ F.W := ca.le_of_image_le _ _ le_rfl hcenter (by rw [htop]; exact le_top)
  have heq : F.W = F.U := le_antisymm inf_le_left hUW
  rw [heq,relIndex_self] at hindex
  omega

theorem source_mathieu_hyperplane_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w))
    (hS : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map
      (ActorCatalogue.starProjection F.H e) = markedSylow.toSubgroup) :
    (mathieuCentralAction F e c he).image F.W = markedPerp := by
  let := chosen.elementary
  let ca := mathieuCentralAction F e c he
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hindex,_⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  exact mathieu_hyperplane_of_index F e c he hS hindex

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Mathieu/Actor.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Mathieu LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem actor_card_of_point_core_at
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    (hdim : finrank (ZMod 2) W = 12)
    (hcore : ∀ (S : Sylow 2 D) (v : W), v ≠ 0 →
      (∀ a : S, σ a.val v = v) →
      Nat.card (pCore 2 (ChapterG.Section10.pointCentralizer σ v)) = 32) (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* D)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] W)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      σ (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    Nat.card (((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection F.H e)) = 32 := by
  obtain ⟨_,hx,B,v,hyp,hline,hfix⟩ :=
    source_terminal_marked_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  let := hx
  let f : F.TerminalHdot ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).trans e
  have hmap (A : Subgroup G) : (F.terminalDot A).map f.toMonoidHom =
      (A.subgroupOf F.H).map (ActorCatalogue.starProjection F.H e) := by
    rw [terminalDot,map_map]
    rfl
  have hact (a : F.TerminalHdot) (w : Additive F.Uhat) :
      σ (f a) (c w) = c (F.terminalRepresentation a w) := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact he b w
  let R : Subgroup D :=
    (F.terminalDot (F.X g)).map f.toMonoidHom
  let C : Subgroup D := ChapterG.Section10.pointCentralizer σ (c v)
  obtain ⟨hRC,hRN⟩ := source_actor_normal_in_point_stabilizer_at d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hyp.point_ne_zero hline
  have hpc : (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).map
      f.toMonoidHom = C := by
    ext b
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (hact a v).trans (congrArg c ha)
    · intro hb
      obtain ⟨a,rfl⟩ := f.surjective b
      exact ⟨a,c.injective ((hact a v).symm.trans hb),rfl⟩
  have hRC' : R ≤ C := (map_mono hRC).trans hpc.le
  have hCN : C ≤ normalizer (R : Set D) :=
    hpc.ge.trans ((map_mono ((normal_subgroupOf_iff_le_normalizer hRC).mp hRN)).trans
      (le_normalizer_map f.toMonoidHom))
  have hpR : IsPGroup 2 R := by
    let : IsElementaryAbelian 2 R := IsElementaryAbelian.map f.toMonoidHom
    exact IsElementaryAbelian.isPGroup 2 R
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  let S : Sylow 2 D :=
    P.mapSurjective (f:=f.toMonoidHom) f.surjective
  have hv : c v ≠ 0 := fun hh =>
    hyp.point_ne_zero (c.injective (hh.trans (map_zero c).symm))
  have hS : ∀ a : S, σ a.val (c v) = c v := by
    have hvP : c v ∈ (fixedSpace F.terminalRepresentation P).map c.toLinearMap :=
      ⟨v,(fun a => hfix a.val a.property),rfl⟩
    exact (fixedSpace_map_equivariant F.terminalRepresentation σ
      f.toMonoidHom c (fun a w => (hact a w).symm) P).le hvP
  have hc : Nat.card (pCore 2 C) = 32 :=
    hcore S (c v) hv hS
  have hu : Nat.card R ≤ 32 := by
    have hh := card_le_of_le (le_pCoreIn_of_normalizes hpR hRC' hCN)
    rw [pCoreIn,card_map_of_injective C.subtype_injective,hc] at hh
    exact hh
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 12 :=
    c.finrank_eq.trans hdim
  have hr := (Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (QuotientGroup.mk'_surjective _)).trans
    (IsElementaryAbelian.rank_le_finrank (p:=2) (F.terminalDot (F.X g)))
  have hb := hyp.dimension_bound.1
  rw [hd] at hb
  have hl : 5 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by omega
  have hpow : Nat.card R = 2 ^ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
    change Nat.card ((F.terminalDot (F.X g)).map f.toMonoidHom) = _
    rw [card_map_of_injective f.injective,Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive (F.terminalDot (F.X g)))
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hl
  exact (congrArg (fun P : Subgroup D => Nat.card P) (hmap _)).symm.trans
    (le_antisymm hu (by simpa only [← hpow] using hp))

theorem source_mathieu_actor_card_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    Nat.card (((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection F.H e)) = 32 := by
  exact actor_card_of_point_core_at ActorCatalogue.Native.action
    Sporadic.Mathieu.M22TripleCover.binarySpace_finrank
    ActorCatalogue.Native.pointCentralizer_core_card d earlier hq chosen structural
    alternatives F hne hZ g hgP hgH e c he

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FullActions.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_full_actions_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (components : EarlierComponentGeneration G)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ X : Subgroup G, X ∈ YFamily F.H T (F.Vi 2) (F.E g) →
      Nonempty (FullMovedSpaceAction T (F.I₂ L) (F.Li L 2) (F.Vi 2) X) ∧
      Quasithin.I5.RankTwoParabolics
        (localJoin (F.Li L 2) X ⊔ (T : Subgroup G) : Subgroup G)
        ((T : Subgroup G).subgroupOf (localJoin (F.Li L 2) X ⊔ (T : Subgroup G)))
        ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf
          (localJoin (F.Li L 2) X ⊔ (T : Subgroup G)))
        ((X ⊔ (T : Subgroup G)).subgroupOf
          (localJoin (F.Li L 2) X ⊔ (T : Subgroup G))) := by
  let := chosen.elementary
  let := source_intersection_elementary_at d earlier hq chosen structural alternatives F hne g hg hgH
  obtain ⟨extraspecial, hI⟩ :=
    source_extraspecial_data_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  exact (source_lemma_14_4_8 components T (d.qtke.evenCharacteristic T) classification
    (source_natural_action_at d earlier hq chosen structural) F g hg extraspecial hI).2.2.2

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Assembly.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction LargerDimension.IntrinsicSource

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

noncomputable def source_marked_system_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (g : G) (hg : g ∈ L)
    (localData : LocalSourceData T L V F g)
    (X : Subgroup G) (hX : X ∈ YFamily F.H T (F.Vi 2) (F.E g))
    (hne : X ≠ F.Li L 1)
    (e₂ : coreQuotient (F.Li L 1 ⊔ X ⊔ (T : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    MarkedSystem L T (F.Li L 1) (F.Li L 2) X := by
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hN := source_natural_flag_at d earlier hq chosen structural F g hg
  have h₁ := source_first_actor_at d earlier hq chosen structural F g hg
  let a₁ := localData.action (F.Li L 1) h₁.1
  let aX := localData.action X hX
  let geo := source_geometry_of_full_actions F.H (normalizer (L : Set G)) L
    (F.Li L 1) (F.Li L 2) (F.Vi 1) (F.Vi 2) V (F.E g) X (F.I₂ L) T
    hN hX hne a₁ aX e₂ localData.unique L.le_normalizer
    (h.sylow_normalizes_at structural) le_rfl
  have eq₁ : Nonempty (coreQuotient (L ⊔ (T : Subgroup G)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
    rw [← h₁.2.2]
    exact ⟨a₁.quotient⟩
  exact markedSystem_of_source_geometry L (F.Li L 1) (F.Li L 2) X
    (normalizer (L : Set G)) T geo eq₁ ⟨e₂⟩ ⟨aX.quotient⟩ localData.unique le_rfl

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/LocalAction.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

def source_local_data_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    LocalSourceData T L V F g := by
  have hlocal := source_full_actions_at d earlier hq chosen structural alternatives
    (source_component_generation d.qtke) classification F hne hZ g hg hgP hgH
  refine ⟨fun X hX => (hlocal X hX).1.some, ?_⟩
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  intro K hK hLK
  exact Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
    show K ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
      from ⟨hK, hLK⟩)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Recognition.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction LargerDimension.IntrinsicSource

open LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem actual_overgroup_of_partner_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (partner : Partner T L V F g) :
    ∃ X : Subgroup G, X ∈ YFamily F.H T (F.Vi 2) (F.E g) ∧ X ≠ F.Li L 1 ∧
      (T : Subgroup G) ≤ actualG0 L T (F.Li L 1) (F.Li L 2) X ∧
      Nonempty (actualG0 L T (F.Li L 1) (F.Li L 2) X ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) := by
  obtain ⟨X, hX, hXne, ⟨e₂⟩⟩ := partner
  let a := source_marked_system_at d earlier hq chosen structural F g hg
    (source_local_data_at d earlier hq chosen structural alternatives classification
      F hne hZ g hg hgP hgH) X hX hXne e₂
  exact ⟨X, hX, hXne, source_T_le_actualG0 L T (F.Li L 1) (F.Li L 2) X,
    a.system.a3_source_recognition⟩

theorem contradiction_of_partner_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (partner : Partner T L V F g) : False := by
  obtain ⟨X, _, _, hT, ⟨e⟩⟩ := actual_overgroup_of_partner_at d earlier hq chosen
    structural alternatives classification F hne hZ g hg hgP hgH partner
  exact source_large_overgroup_exclusion_at d earlier hq chosen structural alternatives
    F hne hZ (by omega) _ hT e

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Mathieu/Partner.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Mathieu LargerDimension.LocalAction.Components

open LargerDimension.Mathieu.ModuleGeometry.Native hiding Group

universe u

variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem source_conjugate_local_geometry_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.X g ≤ (T : Subgroup G) ∧ ⁅F.W, F.X g⁆ ≤ F.E g := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨ι,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm ι hcore hindex
  have hXT := F.X_le_T_of_parabolic_core L g hIG
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN) hsplit
  have hqn := F.binary_source_E_normal_in_core L chosen.normalizes g hgP hgen.symm hcomm
  let := hqn
  have hqe := F.binary_source_quotient_elementary L chosen.normalizes g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  have hpair : ∃ hn : ((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal, letI := hn
      IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸ (F.E g).subgroupOf (F.W ⊔ F.X g)) := by
    have hh : ∃ hn : ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)).Normal, letI := hn
        IsElementaryAbelian 2 (((F.I₂ L).pCoreIn 2 : Subgroup G) ⧸
          (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) := ⟨hqn,hqe⟩
    rwa [hsplit] at hh
  obtain ⟨hn,helem⟩ := hpair
  let := hn
  let := helem
  exact ⟨hXT, F.commutator_W_X_le_E g⟩

private theorem source_point_with_normal_actor_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ v : Additive F.Uhat, v ≠ 0 ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      (∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v) ∧
      IsElementaryAbelian 2 (F.terminalDot (F.X g)) ∧
      F.terminalDot (F.X g) ≤ ChapterG.Section10.pointCentralizer F.terminalRepresentation v ∧
      ((F.terminalDot (F.X g)).subgroupOf
        (ChapterG.Section10.pointCentralizer F.terminalRepresentation v)).Normal := by
  obtain ⟨_,hx,B,v,hyp,hline,hfix⟩ :=
    source_terminal_marked_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  exact ⟨v,hyp.point_ne_zero,hline,hfix,hx,
    source_actor_normal_in_point_stabilizer_at d earlier hq chosen
      structural alternatives F hne hZ g hgP hgH v hyp.point_ne_zero hline⟩

private theorem source_marked_point_geometry_at
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* D) (c : Additive F.Uhat ≃ₗ[ZMod 2] W)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      σ (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w))
    (S : Subgroup D) (w : W)
    (hS : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map
      (ActorCatalogue.starProjection F.H e) = S)
    (hfixed : fixedSpace σ S = Submodule.span (ZMod 2) {w}) :
    (hatSpace F (F.Vi 2)).map c.toLinearMap = Submodule.span (ZMod 2) {w} ∧
      ∃ R : Subgroup D,
        ((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection F.H e) = R ∧
        R ≤ ChapterG.Section10.pointCentralizer σ w ∧
        ChapterG.Section10.pointCentralizer σ w ≤ normalizer (R : Set D) ∧
        IsPGroup 2 R := by
  obtain ⟨v,hv,hline,hfix,hx,hRC,hRN⟩ :=
    source_point_with_normal_actor_at d earlier hq chosen structural alternatives F hne hZ g hgP hgH
  let := hx
  obtain ⟨f,hmap,hact⟩ := terminal_marked_transport σ F
    (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ) e c he
  have hcv : c v = w := point_of_fixed_space_marking F.terminalRepresentation σ
    f.toMonoidHom c (fun a w => (hact a w).symm)
    (F.terminalDot (T : Subgroup G)) S ((hmap (T : Subgroup G)).trans hS)
    v hv hfix w hfixed
  constructor
  · rw [← hline,Submodule.map_span,Set.image_singleton]
    change Submodule.span (ZMod 2) {c v} = _
    rw [hcv]
  · obtain ⟨R,hmapR,hR,hRN,hpR⟩ := normal_point_image F.terminalRepresentation
      σ f c hact v (F.terminalDot (F.X g))
      (((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection F.H e))
      (hmap (F.X g)) hRC hRN
    rw [hcv] at hR hRN
    exact ⟨R,hmapR,hR,hRN,hpR⟩

/- Keep the concrete ATLAS generator certificates behind the proved group API.
Unfolding them while aligning the native subgroup types needlessly evaluates
large finite matrix expressions. This local setting leaves the data unchanged. -/
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel in
attribute [local irreducible] actionGroup unitC unitD matrixC matrixD matrixDInv fromRows
attribute [local irreducible] CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.markedSylow

private theorem partner_of_local_geometry
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hZ : F.ZU = F.Vi 1)
    (g : G)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w))
    (hS : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map
      (ActorCatalogue.starProjection (B := ActorCatalogue.Native.Model) F.H e) = markedSylow.toSubgroup)
    (hcard : Nat.card (((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection (B := ActorCatalogue.Native.Model) F.H e)) = 32)
    [IsExtraspecial 2 F.U]
    (hUT : F.U ≤ (T : Subgroup G))
    (hVE : V ≤ F.E g)
    (hXT : F.X g ≤ (T : Subgroup G)) (hWX : ⁅F.W, F.X g⁆ ≤ F.E g)
    (hpoint : (hatSpace F (F.Vi 2)).map c.toLinearMap =
      Submodule.span (ZMod 2) {markedVector})
    (R : Subgroup ActorCatalogue.Native.Model)
    (hmapR : ((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection (B := ActorCatalogue.Native.Model) F.H e) = R)
    (hR₀ : R ≤ ChapterG.Section10.pointCentralizer ActorCatalogue.Native.action markedVector)
    (hRN₀ : ChapterG.Section10.pointCentralizer ActorCatalogue.Native.action markedVector ≤
      normalizer (R : Set ActorCatalogue.Native.Model))
    (hpR : IsPGroup 2 R)
    (hperp : (mathieuCentralAction F e c he).image F.W = markedPerp)
    (hfirst : F.Li L 1 ∈ YFamily F.H T (F.Vi 2) (F.E g)) : Partner T L V F g := by
  let ca := mathieuCentralAction F e c he
  have hC : ChapterG.Section10.pointCentralizer ActorCatalogue.Native.action markedVector =
      pointCentralizer := RadicalAction.NativePositions.pointCentralizer_eq_reference.symm
  have hR : R ≤ pointCentralizer := hR₀.trans hC.le
  have hRN' : pointCentralizer ≤ normalizer (R : Set ActorCatalogue.Native.Model) :=
    hC.ge.trans hRN₀
  have hT : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map F.H.subtype = T :=
    map_subgroupOf_eq_of_le (F.invariant 1)
  let geom : EarlierGeometry F.H F.U (F.Vi 2) F.W (F.X g) (F.E g)
      (T.subtype (F.invariant 1)) e ca R := {
    core_le_sylow := hUT.trans hT.ge
    point_le_core := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
    center_le_point := by rw [center_point F hZ]; exact comap_mono (F.monotone (by omega : 1 ≤ 2))
    center_le_intersection := by
      rw [center_point F hZ]
      exact comap_mono ((F.le_seed 1).trans hVE)
    hyperplane_le_core := inf_le_left
    conjugate_le_local := hXT.trans (F.invariant 1)
    commutator_le_intersection := hWX
    sylow_marking := hS
    point_marking := hpoint
    hyperplane_marking := hperp
    conjugate_image := hmapR
    conjugate_image_le := hR
    conjugate_image_normal := hRN'
    conjugate_image_two := hpR
    conjugate_image_card := (congrArg (fun P : Subgroup ActorCatalogue.Native.Model => Nat.card P) hmapR).symm.trans hcard }
  rw [← hT] at hfirst
  obtain ⟨X,hneX,hY,hqX⟩ := LargerDimension.Mathieu.exists_partner geom (F.Li L 1) hfirst
  rw [hT] at hY hqX
  refine ⟨X,?_,hneX,hqX⟩
  rw [hY]
  simp

private theorem partner_of_marked_geometry_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w))
    (hS : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map
      (ActorCatalogue.starProjection F.H e) = markedSylow.toSubgroup)
    (hcard : Nat.card (((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection F.H e)) = 32) : Partner T L V F g := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1
  obtain ⟨hXT,hWX⟩ := source_conjugate_local_geometry_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  let ca := mathieuCentralAction F e c he
  obtain ⟨hpoint,R,hmapR,hR₀,hRN₀,hpR⟩ := source_marked_point_geometry_at
    ActorCatalogue.Native.action d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH e c he markedSylow.toSubgroup markedVector hS markedSylow_fixedSpace
  exact partner_of_local_geometry F hZ g e c he hS hcard
    (source_closure_le_sylow_at d earlier hq chosen structural alternatives F)
    (F.seed_le_E_of_normalizes g (chosen.normalizes hg)) hXT hWX
    hpoint R hmapR hR₀ hRN₀ hpR
    (source_mathieu_hyperplane_at d earlier hq chosen structural alternatives F hne g hgP hgH e c he hS)
    (source_first_actor_at d earlier hq chosen structural F g hg).1

theorem source_mathieu_partner_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    Partner T L V F g := by
  obtain ⟨e',c',he',hS⟩ := exists_mathieu_sylow_marking F e c he
  exact partner_of_marked_geometry_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH e' c' he' hS
    (source_mathieu_actor_card_at d earlier hq chosen structural alternatives F hne hZ
      g hgP hgH e' c' he')

theorem source_mathieu_contradiction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    False := by
  exact contradiction_of_partner_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hg hgP hgH
    (source_mathieu_partner_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH e c he)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Mathieu/Recognition.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Theory.GroupTheory

open scoped IsMulCommutative Matrix

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Mathieu

open LargerDimension.LocalAction.Components

open ChapterH.Section10To12

open Sporadic.Mathieu

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_mathieu_component_proper_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hK : IsTripleM22 (generalizedFitting (coreQuotient F.H)))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 12) :
    generalizedFitting (coreQuotient F.H) ≠ ⊤ := by
  intro ht
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,hx,B,v,hyp⟩ := source_terminal_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let := hx
  let e : F.TerminalHdot ≃* M22TripleCover :=
    (QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).trans
      (Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr ht).symm.trans hK.groupEquiv))
  have hr : Group.rank (F.terminalDot (F.X g)) ≤ 4 := by
    have h := Subgroup.rank_le_primeRank 2 (F.terminalDot (F.X g))
      (IsElementaryAbelian.isPGroup 2 (F.terminalDot (F.X g)))
    exact h.trans ((primeRank_congr 2 e).trans_le M22TripleCover.NoFF.twoRank_le_four)
  have hqrank := Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (QuotientGroup.mk'_surjective _)
  have hb := hyp.dimension_bound.1
  rw [hd] at hb
  omega

theorem source_mathieu_coordinates_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hK : IsTripleM22 (generalizedFitting (coreQuotient F.H)))
    (hirr : letI := chosen.elementary
      letI := F.U_normal
      (CoreGeometry.sourceAction F
        (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation.IsIrreducible)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 12) :
    ∃ e : coreQuotient F.H ≃* ActorCatalogue.Native.Model,
    ∃ c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space,
      ∀ (a : F.H) w,
        ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
          c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w) := by
  let := chosen.elementary
  let := F.U_normal
  let s := CoreGeometry.sourceAction F
    (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)
  let : s.representation.IsIrreducible := hirr
  obtain ⟨e,c,hc⟩ := mathieu_coordinates_of_component s.representation s.faithful hd
    _ hK rfl (source_mathieu_component_proper_at d earlier hq chosen structural alternatives F hne hZ hK hd)
  refine ⟨e,c,?_⟩
  intro a w
  exact (hc (QuotientGroup.mk' (pCore 2 F.H) a) w).symm

theorem source_mathieu_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (hK : IsTripleM22 (generalizedFitting (coreQuotient F.H)))
    (hirr : letI := chosen.elementary
      letI := F.U_normal
      (CoreGeometry.sourceAction F
        (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation.IsIrreducible)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 12) : False := by
  obtain ⟨e,c,hc⟩ := source_mathieu_coordinates_at d earlier hq chosen structural alternatives
    F hne hZ hK hirr hd
  obtain ⟨g,hg,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  exact source_mathieu_contradiction_at d earlier hq chosen structural alternatives classification
    F hne hZ hlarge g hg hgP hgH e c hc

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/MathieuComponentExclusion.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension

open LargerDimension.LocalAction.Components

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_no_mathieu_twenty_two_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (e₀ : C ≃* Sporadic.Mathieu.M22) : False := by
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  exact MathieuComponent.not_model hyp h9 e₀

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge


open Subgroup Module Representation Theory.GroupTheory

open scoped IsMulCommutative Matrix

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension

open LargerDimension.LocalAction.Components

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Mathieu

open LargerDimension.LocalAction.Components

open ChapterH.Section10To12

open Sporadic.Mathieu

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_no_triple_mathieu_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (C : Subgroup F.TerminalHdot) [C.Normal]
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (model : Chapter1.Section02.LocalModels.IsM22Cover C)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 12) : False := by
  let hC : IsTripleM22 C := {
    quasisimple := model.1
    center_card := (Nat.card_congr model.2.1.some.toEquiv).trans (by simp)
    centralQuotient := model.2.2 }
  obtain ⟨g,hg,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,hx,B,v,hyp⟩ := source_terminal_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let := hx
  have hproper : C ≠ ⊤ := by
    intro ht
    let e : F.TerminalHdot ≃* M22TripleCover :=
      Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr ht).symm.trans hC.groupEquiv)
    have hr : Group.rank (F.terminalDot (F.X g)) ≤ 4 := by
      have h := Subgroup.rank_le_primeRank 2 (F.terminalDot (F.X g))
        (IsElementaryAbelian.isPGroup 2 (F.terminalDot (F.X g)))
      exact h.trans ((primeRank_congr 2 e).trans_le M22TripleCover.NoFF.twoRank_le_four)
    have hqrank := Group.rank_le_of_surjective
      (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
      (QuotientGroup.mk'_surjective _)
    have hb := hyp.dimension_bound.1
    rw [hd] at hb
    omega
  let := hirr
  obtain ⟨e,c,hc⟩ := mathieu_coordinates_of_normal_irreducible_component
    F.terminalRepresentation F.terminalRepresentation_injective hd C hC hproper
  let q := QuotientGroup.quotientMulEquivOfEq
    (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ).symm
  exact source_mathieu_contradiction_at d earlier hq chosen structural alternatives classification
    F hne hZ hlarge g hg hgP hgH (q.trans e) c (fun a w => (hc _ w).symm)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FixedLineModule.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_fixed_line_module_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) := by
  obtain ⟨hf,hE,hX,_⟩ := source_terminal_ranks_of_no_lowRank_at d earlier hq chosen structural
    alternatives F hne hZ g hgP hgH v hline hn
  rw [← hline] at hf
  obtain ⟨hgen,hbound⟩ := FixedLine.cyclic_and_bound hyp hf
  refine ⟨hgen,?_,?_⟩
  · have hd : 4 < finrank (ZMod 2) (Additive F.Uhat) := by
      have hcenter := (source_extraspecial_order_at d earlier hq chosen structural alternatives
        F hne hZ).1.center_order_p
      have hc : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
        rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hcenter]
        change Nat.card (Additive F.Uhat) * 2 = _
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,pow_succ]
      by_contra hh
      have hb := Nat.pow_le_pow_right (n := 2) (by decide)
        (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 5)
      rw [← hc] at hb
      norm_num at hb
      omega
    have h6 : finrank (ZMod 2) (Additive F.Uhat) ≠ 6 := by
      intro h6
      have hr : Group.rank (F.terminalDot (F.X g)) = 2 := by omega
      rw [FixedLine.elementary_card_eq_rank _,hr,h6] at hbound
      norm_num at hbound
    omega
  · intro h8
    obtain ⟨hc,e,he⟩ := FixedLine.regular_of_degree_eight hyp hf hE hX h8
    exact ⟨hc,e,he,FixedLine.movedRank_of_regular e he hc h8⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/SingleComponentFixedLine.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative



namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension

open LargerDimension.LocalAction.Components

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_large_single_component_six_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) :
    finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
      (Nonempty (C ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2)))) := by
  have hsmall : Nonempty (C ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
    rcases source_large_single_component_models_at d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH C hC hm hirr with ⟨_,he | he | hf⟩ | hc
    · exact .inl he
    · exact .inr he
    · exact (source_no_mathieu_twenty_two_component_at d earlier hq chosen structural alternatives
        F hne g hgP hgH C hC hm hirr hf.2.some).elim
    · exact (source_no_triple_mathieu_component_at d earlier hq chosen structural alternatives
        classification F hne hZ hlarge C hirr hc.1 hc.2).elim
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  have hlt : finrank (ZMod 2) (Additive F.Uhat) < 8 :=
    Nat.lt_of_not_ge (fun hd => not_small_component_of_degree_ge_eight h9 hd hsmall)
  have hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
    have hcenter := (source_extraspecial_order_at d earlier hq chosen structural alternatives
      F hne hZ).1.center_order_p
    have hc : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
      rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hcenter]
      change Nat.card (Additive F.Uhat) * 2 = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,pow_succ]
    by_contra hn
    have hb := Nat.pow_le_pow_right (n := 2) (by decide)
      (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 6)
    rw [← hc] at hb
    norm_num at hb
    omega
  have heven := AlternatingForm.even_finrank B hyp.alternating hyp.nondegenerate
  exact ⟨by obtain ⟨n,hn⟩ := heven; omega,hsmall⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/SmallComponentReduction.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Theory.GroupTheory

open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_no_alternating_seven_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hd : finrank (ZMod 2) (Additive F.Uhat) = 6)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (e₀ : C ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨_,_,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  let P := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hHc : F.H ≤ centralizer (F.ZU : Set G) := by
    rw [hZ]
    exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hD : D = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact mem_map_of_mem _ (hHc b.property)
  have hu := CaseOneHS.source_center_centralizing_point_image_three_rank_le_one_at
    d earlier hq chosen structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (P.subgroupOf D) ≤ 1 at hu
  have hpD : P ≤ D := by rw [hD]; exact le_top
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe hpD)] at hu
  exact SevenComponent.not_seven_of_point_rank_le_one hyp h9 (by omega)
    (map_mono (fun _ hx => F.conjugate_ZU_le_X g hx)) hu e₀

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension

open LargerDimension.LocalAction.Components

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_large_single_component_binary_g2_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) :
    finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
      Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨hd,he | he⟩ := source_large_single_component_six_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH C hC hm hirr
  · exact (source_no_alternating_seven_component_at d earlier hq chosen structural alternatives
      F hne hZ hd g hgP hgH C hC hm hirr he.some).elim
  · exact ⟨hd,he⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/ComponentOrbitRecognition.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_no_binary_g2_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 6)
    (C : Subgroup F.TerminalHdot)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (e₀ : C ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  let := chosen.elementary
  let c := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  obtain ⟨g, _, hgP, hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  let q := F.uhatQuadraticForm (by decide) c.two c.frattini_point
    (center_frattini_bot_of_center_point F c hZ)
  obtain ⟨_, hqi, hqn⟩ := quadratic_intersection_of_center_point F c (by decide) hZ g
    (disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L chosen.normalizes
      c.seed_center g hgP hgH).1)
  have hterminal (a : F.TerminalHdot) (w : Additive F.Uhat) :
      q (F.terminalRepresentation a w) = q w := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact hqi a w.toMul
  let σ := (F.terminalRepresentation.comp C.subtype).comp e₀.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e₀.symm.toMonoidHom e₀.symm.surjective _).mpr hirr
  obtain ⟨a, f, hf⟩ :=
    ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix.quasiequivalent_of_finrank_eq_six σ hd
  have htrans : ∀ x y : Additive F.Uhat, x ≠ 0 → y ≠ 0 → ∃ b, σ b x = y := by
    intro x y hx hy
    obtain ⟨b, hb⟩ := Atlas.G2.Natural.derivedAction_transitive (ZMod 2) (f x) (f y)
      (fun hz => hx (f.map_eq_zero_iff.mp hz)) (fun hz => hy (f.map_eq_zero_iff.mp hz))
    refine ⟨a.symm b, f.injective ?_⟩
    rw [hf, a.apply_symm_apply]
    exact hb
  exact not_nondegenerate_quadratic_of_nonzero_transitive σ (by omega) htrans q
    (fun a w => hterminal (e₀.symm a) w) hqn

theorem source_no_normal_irreducible_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) : False := by
  obtain ⟨hd, ⟨e⟩⟩ := source_large_single_component_binary_g2_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH C hC hm hirr
  exact source_no_binary_g2_component_at d earlier hq chosen structural alternatives F hne hZ hd C hirr e

theorem source_large_irreducible_orbit_natural_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C (componentOrbit C ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) :
    ∃ n : ℕ, 1 < n ∧ ChapterG.Section09.Quasiequivalent
      (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype)
      (ChapterG.Section09.TwoComponents.fourOrthogonal n) := by
  have hproper : componentOrbit C ⊤ ≠ C := by
    intro he
    have h9' : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
        F.terminalRepresentation (F.terminalDot (F.X g)) C C
        (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
      simpa only [he] using h9
    let := h9'.normal_H
    exact source_no_normal_irreducible_component_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH C hC hm h9'.irreducible
  obtain ⟨_, _, B, v, hyp⟩ := source_terminal_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  obtain ⟨C₂,hC₂,hH,hCC₂,⟨e⟩,hz,hmrank,td,hk⟩ :=
    ChapterG.Section11.WholePair.component_pair_data h9 hproper
      (AlternatingForm.even_finrank B hyp.alternating hyp.nondegenerate)
  obtain ⟨_,hn,hmodel⟩ := ChapterG.Section11.WholePairNatural.recognition h9
    hC₂ hH hCC₂ e hz td hmrank hk
  exact ⟨td.n,hn,hmodel⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end
