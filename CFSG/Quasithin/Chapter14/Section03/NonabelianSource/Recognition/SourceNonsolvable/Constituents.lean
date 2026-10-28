module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Source
public import CFSG.Quasithin.ChapterG.Section10.Components.Orthogonal

/-!
# Component constituents on the original nonsolvable rank-two terminal action

The original 14.3.11 setup supplies G.10 for the literal terminal quotient
H/ker(terminalHatAction), on U/Z(U). The nonsolvable branch is irreducible.
Given G.11.5's Fitting-centralizer intersection, the G.10.6--7 reduction selects
an actual component moved by the literal dotted X and constructs its normal
orbit constituent on the original module and alternating form.

The only additional premise is the G.11.5 intersection. This is the input
owned by the earlier Fitting argument, and is retained explicitly until its
source proof is assembled. The component catalogue and the lift to an ambient
local component are subsequent statements, not conclusions asserted here.
Source: Aschbacher--Smith, G.10.6--7 and 14.3.15, printed pp.359,995.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original source prefix constructs the literal moved component and its
constituent. G.11.5 is the remaining Fitting-centralizer input. -/
theorem source_terminal_moved_component_constituents
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
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    (hF : F.terminalDot (F.X g) ⊓
      centralizer (fittingSubgroup F.TerminalHdot : Set F.TerminalHdot) ≠ ⊥) :
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat), ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
        ⁅L, F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ComponentOrbitConstituents F.terminalRepresentation B L := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨_,_,hx,B,v,hyp,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := hx
  exact ⟨hx,B,v,hyp,hyp.exists_moved_component_constituents hn hF⟩

/-- The original source selects the A.1.42 homogeneous constituent, whose
orbit under the literal dotted X is independent in the original hat module. -/
theorem source_terminal_moved_component_selection
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
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    (hF : F.terminalDot (F.X g) ⊓
      centralizer (fittingSubgroup F.TerminalHdot : Set F.TerminalHdot) ≠ ⊥) :
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat), ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
        ⁅L, F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ComponentOrbitSelection F.terminalRepresentation B L (F.terminalDot (F.X g)) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨_,_,hx,B,v,hyp,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := hx
  exact ⟨hx,B,v,hyp,hyp.exists_moved_component_selection hn hF⟩

/-- The original source selects the A.1.42 homogeneous constituent, whose
orbit under the literal dotted X is independent in the original hat module. -/
theorem source_terminal_moved_component_orthogonal_selection
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
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    (hF : F.terminalDot (F.X g) ⊓
      centralizer (fittingSubgroup F.TerminalHdot : Set F.TerminalHdot) ≠ ⊥) :
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat), ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
        ⁅L, F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ComponentOrbitSelection F.terminalRepresentation B L (F.terminalDot (F.X g)) ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨_,_,hx,B,v,hyp,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := hx
  exact ⟨hx,B,v,hyp,hyp.exists_moved_component_orthogonal_selection hn hF⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
