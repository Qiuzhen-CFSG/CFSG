module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingNontrivialCardSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingCentralizerComponentSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.FullSylow
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# Exclusion of the original nontrivial alternating-five block centralizer

The actual block centralizer D has order two, so C_G(D) is a two-local
SQTK group. Its original selected Sylow has order at most 256. The source
component containing the alternating-five block retains that full-Sylow
local marking and normalization. The centerless block intersects the
component center trivially, and the intrinsic full-Sylow model exclusion
now gives the contradiction. Every component and model premise is
discharged from the original source hypotheses.

Source: Aschbacher–Smith 2.4.29, printed p.545, the D nontrivial paragraph.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem MinimalBlockSetup.single_alternating_nontrivial_centralizer_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hne : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) ≠ ⊥) : False := by
  let L := d.block.map d.H.subtype
  let D := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let C := centralizer (D : Set G)
  let A := L.subgroupOf C
  obtain ⟨hHC,_,_,_⟩ :=
    d.single_alternating_nontrivial_centralizer_core hG T hM hTM hu hST hsingle hA hne
  have hLC : L ≤ C := (map_subtype_le _).trans hHC
  obtain ⟨S,K,hS,hK,_hKn,hAK,hlocal,hn,hself,hc⟩ :=
    d.single_alternating_nontrivial_centralizer_component hG T hM hTM hu hST hsingle hA hne
  have hDcard : Nat.card D = 2 := by
    have hh := d.single_alternating_centralizer_card_le_two hG T hM hTM hu hST hsingle hA
    change Nat.card D ≤ 2 at hh
    have hp : 0 < Nat.card D := Nat.card_pos
    have hn : Nat.card D ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    omega
  have hCtwo : IsTwoLocal C := ⟨D,hne,T.isPGroup'.to_le inf_le_left,
    le_antisymm (Subgroup.centralizer_le_normalizer _) (normalizer_le_centralizer_of_card_two D hDcard)⟩
  have hSc : Nat.card S ≤ 256 := by
    rw [←card_map_of_injective C.subtype_injective,hS]
    exact d.single_alternating_sylow_card_le_256 hG T hM hTM hu hST hsingle hA
  let e := subgroupOfEquivOfLe hLC
  have hAC : IsAlternatingBlock A 5 := hA.of_mulEquiv e.symm
  have hAc : Nat.card ((blockU A).map A.subtype) = 16 := by
    rw [card_map_of_injective A.subtype_injective]
    rw [←card_map_of_injective (f:=e.toMonoidHom) e.injective,RankOne.Solvable.blockU_map_equiv e]
    change Nat.card ((blockU L).map L.subtype) = 16 at hc
    simpa only [card_map_of_injective L.subtype_injective] using hc
  have hAz : Disjoint (A.subgroupOf K) (center K) := by
    apply disjoint_def.mpr
    intro x hx hz
    apply Subtype.ext
    apply Subtype.ext
    apply disjoint_def.mp hself hx
    intro l hl
    exact congrArg (fun w : K => ((w:C):G))
      ((mem_center_iff.mp hz) ⟨⟨l,hLC hl⟩,hAK hl⟩)
  exact AlternatingTerminal.no_containing_component_full_sylow (hG.twoLocal_sqtk hCtwo)
    S hSc A hAC hAc hlocal.1 hn K hK hAK hAz
end CFSG.Quasithin.Chapter2
