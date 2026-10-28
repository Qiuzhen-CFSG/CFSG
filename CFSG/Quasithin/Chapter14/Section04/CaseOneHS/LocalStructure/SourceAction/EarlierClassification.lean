module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.EarlierNontrivial
public import CFSG.Quasithin.ChapterG.Section11.ExchangedModelReduction

/-!
# The original nonextraspecial flag in the low-rank action reduction

The conjugate center acts trivially on W-hat/V₂-hat by the earlier
commutator bound. Its newly proved nontrivial dotted image therefore
supplies a nonidentity section-centralizer element. The symplectic
calculation gives an actual actor of rank at most two whose moved space
contains the marked point, even when the whole actor fixes only that line.

Applying the existing G.11 reduction retains the literal form, point,
intersection, actor, Sylow normality, components and constituent coordinates.
The half-degree bound excludes its solvable six-dimensional remainder.
Recognition of the remaining whole and exchanged nonsolvable actions is
still required before the full marked 14.3.24 alternatives can be asserted.
In particular the exceptional exchanged GL₄(2) action has not been silently
removed from the reduction.

Source: Aschbacher--Smith, 12.8.10(4), 12.8.11(6), 12.8.13(4),
14.3.12--14 and 14.3.24, printed pp.853--856,993--994,1000.
The exhaustive corrected G.11 theorem remains with
qt-g112-low-rank-symplectic-classification; the original HS alternatives,
their exclusions and natural coordinates remain with qt-d-hs-action-source.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original conjugate center centralizes the marked hyperplane modulo its line. -/
theorem source_earlier_center_le_section_centralizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.terminalDot (conjugate F.ZU g) ≤ Xdot₀ F F.terminalHatAction g := by
  let := chosen.elementary
  obtain ⟨htwo,hphi,hvc⟩ := source_closure d earlier hq chosen structural alternatives F hne
  obtain ⟨hcomm,_⟩ := CaseOneLarge.source_commutator_squares d earlier hq chosen structural alternatives F
  let C := F.localKernel_markedForm (by decide) htwo hphi hcomm
  have hb := F.center_commutator_le_plane (by decide) L chosen.normalizes hvc hcomm
    (F.plane_centralizer_center C) g hgP hgH
  rw [commutator_comm] at hb
  rintro x ⟨a,ha,rfl⟩
  exact mem_Xdot₀_of_displacement F F.terminalHatAction F.terminalHatAction_apply_mk g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP) a (F.conjugate_ZU_le_X g ha)
    (fun w hw => hb (commutator_mem_commutator ha hw))

/-- A nonextraspecial rank-three flag supplies the low-rank classifier's actual
witness, without requiring its whole actor to have a larger fixed space. -/
theorem source_earlier_lowRank (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat) (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  let := chosen.elementary
  have hsec : Xdot₀ F F.terminalHatAction g ≠ ⊥ := by
    intro he
    exact source_earlier_conjugate_center_ne_bot d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH
      (le_bot_iff.mp (he ▸ source_earlier_center_le_section_centralizer d earlier hq chosen
        structural alternatives F hne g hgP hgH))
  obtain ⟨htwo,hphi,hvc⟩ := source_closure d earlier hq chosen structural alternatives F hne
  obtain ⟨hcomm,_⟩ := CaseOneLarge.source_commutator_squares d earlier hq chosen structural alternatives F
  let C := F.localKernel_markedForm (by decide) htwo hphi hcomm
  have hzero (a b : F.U) : C.form (hatElement F a) (hatElement F b) = 0 ↔ Commute a b := by
    rw [show C.form (hatElement F a) (hatElement F b) =
      (C.valueEquiv ⟨⁅(a:G),(b:G)⁆,hcomm (commutator_mem_commutator a.property b.property)⟩).toAdd
        from C.evaluation a b]
    change C.valueEquiv _ = 1 ↔ _
    rw [map_eq_one_iff C.valueEquiv C.valueEquiv.injective,Subtype.ext_iff]
    exact commutatorElement_eq_one_iff_mul_comm.trans (by
      change (a:G)*(b:G)=(b:G)*(a:G) ↔ a*b=b*a
      exact ⟨fun he => Subtype.ext he, fun he => congrArg (fun t : F.U => (t:G)) he⟩)
  have hi : ∀ (a : F.H) (u w : F.Uhat),
      C.form (Additive.ofMul (F.terminalHatAction a u)) (Additive.ofMul (F.terminalHatAction a w)) =
        C.form (Additive.ofMul u) (Additive.ofMul w) := by
    intro a u w
    change F.uhatBilinearForm (by decide) htwo hphi
      (Additive.ofMul (F.uhatAction a u)) (Additive.ofMul (F.uhatAction a w)) = _
    rw [F.uhatBilinearForm_apply,F.uhatCommutator_invariant (by decide) htwo hphi]
    rfl
  obtain ⟨x,hx,_,hr,hm⟩ := exists_lowRank_of_Xdot₀_ne_bot F (by decide) hvc
    F.terminalHatAction g C.form C.nondegenerate C.alternating hzero hi hsec
  exact ⟨x,hx,hr,hm (hline ▸ Submodule.mem_span_singleton_self v)⟩

/-- Apply the existing genuine G.11 reduction on the original flag. The
solvable degree-six remainder is excluded by the source half-degree bound;
recognition of the whole and exchanged nonsolvable actions remains open. -/
theorem source_earlier_marked_model_reduction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      (ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ChapterG.Section11.WholeOrExchangedModelReduction F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hcover,hn,_⟩ :=
    source_earlier_classification_input d earlier hq chosen structural alternatives F hne g hgP hgH
  let := heU
  let := heX
  have hw := source_earlier_lowRank d earlier hq chosen structural alternatives F hne hZ g hgP hgH v hline
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases ChapterG.Section11.conclusion_or_whole_or_exchanged_models hyp hcover hw hn with
    hc | ⟨hi,hd,hsol | hnon⟩
  · exact Or.inl hc
  · have hb := source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
      F g hne hZ hgP hgH
    obtain ⟨_,hr,hd⟩ := hsol
    omega
  · exact Or.inr ⟨hi,hd,hnon⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
