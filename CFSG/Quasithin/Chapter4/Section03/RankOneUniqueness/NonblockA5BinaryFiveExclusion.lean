module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesBinaryPreparation
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5SmallExclusions
public import Theory.SpecificGroups.BinaryLinear.RankOneNormalSections

/-!
# The actual SL₅(2) star row is impossible for the original A₅ seed

The literal star image of L is perfect and normal in the original star
local, and its two-core quotient is A₅. That proper local contains a full
Sylow subgroup of the star component. The binary five-space parabolic
obstruction therefore excludes an SL₅(2) marking of this same component.

The source seed quotient supplies the required normal subgroup directly;
no block hypothesis or full component-quotient marking is needed.
Source: Aschbacher--Smith C.4.1(4), C.4.5 and original 4.3.7,
pp.151--153 and 615--616, in the A₅ case.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- An SL₅(2) marking of the original constrained star component contradicts
the literal normal A₅ seed, without a block assumption. -/
theorem not_linearFiveTwo_star_of_a5
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (a : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* SL(5,ZMod 2)) : False := by
  let C := starImage (K c) (c.I.pCoreIn 2) (K c)
  let P := (starM (K c) (c.I.pCoreIn 2)
    (c.H ⊓ normalizer (L : Set G))).subgroupOf C
  let A := (L.subgroupOf (K c)).map (toStarImage (K c) (c.I.pCoreIn 2))
  have hn : (L.subgroupOf (c.H ⊓ normalizer (L : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer inf_le_right
  obtain ⟨hAP,hAn,hAc⟩ := c.c28.constrained_normal_star_seed_component hn
    c.K c.component c.quotient c.block_source_outside hf
  obtain ⟨aA⟩ := c.c28.constrained_normal_a5_star_seed_quotient hn a
    c.K c.component c.quotient c.block_source_outside hf
  let E := e.trans (slEquivLinear 5)
  let N := P.map E.toMonoidHom
  let B := A.map E.toMonoidHom
  have hBN : B ≤ N := map_mono hAP
  have hNB : N ≤ normalizer (B : Set _) := by
    rw [←map_equiv_normalizer_eq A E]
    exact map_mono ((normal_subgroupOf_iff_le_normalizer hAP).mp hAn)
  let f : A →* N := (E.toMonoidHom.comp A.subtype).codRestrict N
    (fun x => hBN (mem_map_of_mem E.toMonoidHom x.property))
  have hfi : Function.Injective f := by
    intro x y he
    exact Subtype.ext (E.injective (congrArg Subtype.val he))
  have hr : f.range = B.subgroupOf N := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact mem_map_of_mem E.toMonoidHom x.property
    · rintro ⟨z,hz,he⟩
      exact ⟨⟨z,hz⟩,Subtype.ext he⟩
  let : (B.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNB
  let : f.range.Normal := hr.symm ▸ inferInstanceAs (B.subgroupOf N).Normal
  let : Group.IsPerfect (A.subgroupOf P) := hAc.perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAP).toMonoidHom) (subgroupOfEquivOfLe hAP).surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := aA.isSimpleGroup
  have hc : Nat.card (A ⧸ pCore 2 A) = 60 := by
    rw [Nat.card_congr aA.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hN : N ≠ ⊤ := by
    intro he
    have hh := map_injective E.injective
      (he.trans (map_top_of_surjective _ E.surjective).symm)
    exact (C27Source.star_thompson_intersection_from_source
      (c.block_source_input hf)).2.not_ge (subgroupOf_eq_top.mp hh)
  obtain ⟨U,hU⟩ := c.block_star_local_sylow
  exact BinaryLinear.RankOneNormalSections.no_normal_sixty_in_five_sylow_overgroup
    (U.mapSurjective E.surjective) N (map_mono hU) hN hc f hfi

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
