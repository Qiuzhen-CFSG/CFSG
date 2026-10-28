module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Constituents
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Lifting
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NonfaithfulFitting
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.TerminalPointSylow
public import CFSG.Quasithin.ChapterG.Section10.Components.Hyperplane
/-!
# The original nonsolvable component extraction

The original rank-two setup constructs G.10 on its actual terminal action.
The proved G.11.5 theorem supplies a moved component. Its normal orbit carries
an independent homogeneous constituent orbit and the adapted orthogonal
pairing. The original quotient Sylow normalizes the actor and fixes the marked
point, while residual generation in the original point normalizer supplies
the literal ambient local-component lift and the two-conjugate orbit bound.

All hypotheses of this extraction come from the original selected source
context; no Fitting-centralizer, component catalogue or solvable-kernel premise
is added. The subsequent G.10.15 constituent classification and component-row
sieve remain separate conclusions.
Source: Aschbacher--Smith G.10.6--8,G.11.5 and14.3.15, printed pp.359--360,365,994.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Genuine original component extraction, including G.11.5, the G.10.8
orbit and point-Sylow marks, and the exact local lift through the terminal map.
No component catalogue or Fitting-centralizer input is assumed. -/
theorem source_terminal_component_extraction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat), ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      (let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
        (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
       (P : Subgroup F.TerminalHdot) ≤ ChapterG.Section10.pointCentralizer F.terminalRepresentation v ∧
       F.terminalDot (F.X g) ≤ (P : Subgroup F.TerminalHdot) ∧
       ((F.terminalDot (F.X g)).subgroupOf (P : Subgroup F.TerminalHdot)).Normal) ∧
      ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
        ⁅L, F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ComponentOrbitSelection F.terminalRepresentation B L (F.terminalDot (F.X g)) ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
        (normalizer (L : Set F.TerminalHdot)).index ≤ 2 ∧
        ∃ K : Subgroup G, K ≤ F.H ∧ K ∈ MainForward.localComponents T ∧
          (K.subgroupOf F.H).IsCComponent ∧
          (K.subgroupOf F.H).map (QuotientGroup.mk' F.terminalHatAction.ker) = L ∧
          (normalizer (K : Set G)).relIndex F.H ≤ 2 ∧
          ((conjugateSpanBy K (T : Subgroup G)).subgroupOf F.H).Normal := by
  have hF := original_terminal_fitting_centralizer_ne_bot
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn
  obtain ⟨hx,B,v,hyp,L,hL,hm,hs,ho⟩ :=
    source_terminal_moved_component_orthogonal_selection
      hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hF
  let := hx
  exact ⟨hx,B,v,hyp,source_terminal_actor_normal_in_point_sylow
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hyp,
    L,hL,hm,hs,ho,terminal_component_normalizer_index_le_two hG F (by decide) L hL,
    terminal_component_lift hG F (by decide) L hL⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
