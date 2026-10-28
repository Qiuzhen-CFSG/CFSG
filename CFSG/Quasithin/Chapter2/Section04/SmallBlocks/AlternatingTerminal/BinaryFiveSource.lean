module

public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.NormalizerTransfer
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.BinaryFive
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# Binary-five exclusion for the original paired-block persistence input

The proved trivial multiplier recovers the whole containing perfect group
from its literal central-quotient model. The original block and its
commutator layer pass through this same isomorphism. The canonical
normalizer obstruction then lifts to the original group and original
half-Sylow actor, contradicting source persistence.

Source: Aschbacher–Smith 2.4.25, printed p.543, the binary-five catalogue row.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original persistence configuration excludes the actual binary-five
component, retaining its marked central-quotient model. -/
theorem MinimalBlockSetup.alternating_no_binary_five_component
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    {R K : Subgroup G} [Group.IsPerfect K]
    (hRS : R ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hi : R.relIndex ((d.S : Subgroup d.H).map d.H.subtype) = 2)
    (hR : R ∈ beta M)
    (hL : d.block.map d.H.subtype ∈ Chapter1.L G R)
    (hLK : d.block.map d.H.subtype ≤ K)
    (hRK : R ≤ normalizer (K : Set G))
    (hRL : R ≤ normalizer (d.block.map d.H.subtype : Set G))
    (hA : ChapterC.IsAlternatingBlock ((d.block.map d.H.subtype).subgroupOf K) 5)
    (hc : Nat.card ((ChapterC.blockU ((d.block.map d.H.subtype).subgroupOf K)).map
      ((d.block.map d.H.subtype).subgroupOf K).subtype) = 16)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 5 2) : False := by
  classical
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let b : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let eK : K ≃* BinaryLinear.OuterCyclic.LinearGroup 5 :=
    ((PerfectCentralCovering.centralQuotientEquivOfUniversalKernelEqBot
      (Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot F hF)
      a).trans (Atlas.fieldEquivPSL 5 b)).trans
        (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))
  let A := (d.block.map d.H.subtype).subgroupOf K
  let B := A.map eK.toMonoidHom
  have hB : ChapterC.IsAlternatingBlock B 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv (eK.subgroupMap A) hA
  have hBU : (ChapterC.blockU B).map B.subtype =
      ((ChapterC.blockU A).map A.subtype).map eK.toMonoidHom := by
    change (ChapterC.blockU (A.map eK.toMonoidHom)).map (A.map eK.toMonoidHom).subtype = _
    rw [←ChapterC.RankOne.Solvable.blockU_map_equiv
      (A.equivMapOfInjective eK.toMonoidHom eK.injective),map_map,map_map]
    rfl
  have hBc : Nat.card ((ChapterC.blockU B).map B.subtype) = 16 := by
    rw [hBU,card_map_of_injective eK.injective]
    exact hc
  obtain ⟨hN,_,hbad⟩ := AlternatingTerminal.binary_five_normalizer_obstruction B hB hBc
  obtain ⟨hNK,hbadK⟩ := AlternatingTerminal.normalizer_obstruction_of_equiv eK A hN hbad
  exact d.alternating_no_component_normalizer_obstruction hG T hTM hu hRS hi hR hL
    hLK hRK hRL hNK hbadK
end CFSG.Quasithin.Chapter2
