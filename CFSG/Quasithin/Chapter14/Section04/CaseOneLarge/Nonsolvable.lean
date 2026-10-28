module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Solvable
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedPoint
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Lifting
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction
public import CFSG.Quasithin.ChapterG.Section10.NonfaithfulFittingSource
public import CFSG.Quasithin.ChapterG.Section10.Components.Orthogonal
public import CFSG.Quasithin.ChapterG.Section10.Components.Homogeneous
public import CFSG.Quasithin.ChapterG.Section10.Components.Source

/-!
# The nonsolvable component reduction on the original large-case action

The original parabolic generation puts the elementary conjugate actor in
its actual quotient Sylow and proves relative normality. The solvable-case
exclusion and G.11.5 then select a genuinely moved component. Its independent
constituent orbit and orthogonal pairing live on the original U/Z(U), and
lifting through the defining action map gives an actual ambient C-component.
The SQTK cover bounds its conjugate orbit by two.

The marked-constituent consumer constructs G.9.3 in the nondegenerate branch.
These are the source reductions preceding the nonsolvable rows of 14.4.2;
the marked-model classification and partner construction remain unfinished.

Source: Aschbacher--Smith, 12.8.12(2), G.10.7--15, G.11.5--7 and 14.4.2,
printed pp.855,359--366,1006--1007.
-/

public noncomputable section
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

/-- The original conjugate actor is normal in the image of the specified T.
Normality is relative to that Sylow, not to the whole terminal group. -/
theorem source_terminal_actor_normal_in_sylow (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    F.terminalDot (F.X g) ≤ (P : Subgroup F.TerminalHdot) ∧
      ((F.terminalDot (F.X g)).subgroupOf (P : Subgroup F.TerminalHdot)).Normal := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨e, _, hgen, _, hIG, hIN, _, _, hfactor, hPH, hcore, hindex, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  have hcore' := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  exact Xdot_normal_in_Tdot F (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex) L g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hIG
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN) hcore'
    F.terminalHatAction F.terminalHatAction_apply_mk

/-- G.11.5 on the original large-case action, with its solvability and SQTK
premises supplied by the counterexample. -/
theorem source_large_fitting_centralizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.terminalDot (F.X g) ⊓
      centralizer (fittingSubgroup F.TerminalHdot : Set F.TerminalHdot) ≠ ⊥ := by
  obtain ⟨_, heX, B, v, hyp⟩ :=
    source_terminal_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  exact hyp.fitting_centralizer_ne_bot_of_not_solvable (source_terminal_cover F d chosen)
    (source_large_terminal_not_solvable d earlier hq chosen structural alternatives F hne hZ hlarge)

/-- Select and lift an actual moved component, retaining its original
constituents, alternating form, quotient map and relative normality. -/
theorem source_large_component_extraction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat), ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
          Submodule.span (ZMod 2) {v} ∨
        ∃ a : F.terminalDot (F.X g), a ≠ 1 ∧
          finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - LinearMap.id)) ≤ 2 ∧
          v ∈ LinearMap.range (F.terminalRepresentation a - LinearMap.id)) ∧
      (let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
        (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
       (P : Subgroup F.TerminalHdot) ≤ ChapterG.Section10.pointCentralizer F.terminalRepresentation v ∧
       F.terminalDot (F.X g) ≤ (P : Subgroup F.TerminalHdot) ∧
       ((F.terminalDot (F.X g)).subgroupOf (P : Subgroup F.TerminalHdot)).Normal) ∧
      ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
        ⁅C, F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ComponentOrbitSelection F.terminalRepresentation B C (F.terminalDot (F.X g)) ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
        (normalizer (C : Set F.TerminalHdot)).index ≤ 2 ∧
        ∃ K : Subgroup G, K ≤ F.H ∧ K ∈ MainForward.localComponents T ∧
          (K.subgroupOf F.H).IsCComponent ∧
          (K.subgroupOf F.H).map (QuotientGroup.mk' F.terminalHatAction.ker) = C ∧
          (normalizer (K : Set G)).relIndex F.H ≤ 2 ∧
          ((conjugateSpanBy K (T : Subgroup G)).subgroupOf F.H).Normal := by
  let := chosen.elementary
  obtain ⟨heU, hx, B, v, hyp, hline, hfix⟩ :=
    source_terminal_marked_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let := hx
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives F hne hZ hlarge
  have hF := source_large_fitting_centralizer d earlier hq chosen structural alternatives F hne hZ hlarge g hgP hgH
  obtain ⟨C, hC, hm, hs, ho⟩ := hyp.exists_moved_component_orthogonal_selection hn hF
  exact ⟨heU, hx, B, v, hyp, hline,
    source_terminal_fixed_point_alternative d earlier hq chosen structural alternatives F hne g hgP hgH v hline,
    ⟨hfix, source_terminal_actor_normal_in_sylow d earlier hq chosen structural alternatives F hne g hgP hgH⟩,
    C, hC, hm, hs, ho, terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC,
    terminal_component_lift d.qtke F (by decide) C hC⟩

/-- A nondegenerate constituent containing the marked point is the whole
module, so the original representation itself satisfies G.9.3. The exact
constituent selection remains explicit for the subsequent model case split. -/
theorem source_large_componentHypothesis_of_nondegenerate (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C, F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I)
    (hv : v ∈ I) (hnd : (B.restrict I).Nondegenerate) :
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C (componentOrbit C ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP, hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have hd := hyp.constituent_isotropic_or_top_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  have hi : IsIrreducible (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype) := by
    rcases hd with hiso | ⟨_, hirr⟩
    · have hz : (⟨v, hv⟩ : I) = 0 := hnd.1 ⟨v, hv⟩ (fun w => hiso v hv w w.property)
      exact (hyp.point_ne_zero (congrArg Subtype.val hz)).elim
    · exact hirr
  exact hyp.componentHypothesis_of_orbit_irreducible
    (source_terminal_cover F d chosen) hC hm hind hi

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
