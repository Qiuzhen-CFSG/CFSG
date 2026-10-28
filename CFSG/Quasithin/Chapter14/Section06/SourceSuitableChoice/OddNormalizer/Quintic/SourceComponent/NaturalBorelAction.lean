module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.NaturalJoin
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarBorelActors
public import Theory.GroupAction.PrimeCoreOuterKernel
public import Theory.SpecificGroups.PSL2.BinaryOuter
/-!
# Excluding the marked natural row in the quintic comparison

The marked Borel normalizes the literal first-factor action. An outer image of
order divisible by five makes its inner intersection a 2-group: this follows
from the first-factor quotient of order five, while the perfect PSL₂(16)
alternative has trivial solvable outer image. The binary Borel calculation
then forces the actor to be inner, contradicting the outer order-five actor.
Rank zero supplies that actor directly; at rank one the existing joined-factor
comparison supplies it after excluding the inner alternative.

Source: Aschbacher--Smith 14.6.15, printed p.1035. These comparisons use the
actual quotient action and do not require the disputed ordinary-centralizer
identity. The quintic-exclusion owner retains construction of NormalizerGeometry
and selection of the source rows before assembling p = 3; the suitable-element
odd-normalizer owner retains discharge of the earlier 14.6.12–14 inputs.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped commutatorElement Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- The marked source Borel normalizes the literal first-factor actor. -/
theorem source_borel_normalizes_first_actor
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G)) :
    (((starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G))).subgroupOf
      (starImage j.J (Mc.pCoreIn 2) j.J)).map MulAut.conj) ≤
    normalizer (((d.K1.subgroupOf
      (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G))).map
      (starComponentAction j.J (Mc.pCoreIn 2))) : Set _) := by
  have hh := source_intersection_star_normalizes_first s d j hn
  rintro α ⟨x,hx,rfl⟩
  apply hh
  refine mem_map_of_mem MulAut.conj ?_
  change (x : StarQuotient j.J (Mc.pCoreIn 2)) ∈
    starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G)) at hx
  obtain ⟨b,hb,he⟩ := hx
  let k : j.J := ⟨b,hb.2⟩
  refine ⟨k,⟨le_conjugateSpanBy _ _ hb.2,hb.1⟩,?_⟩
  exact Subtype.ext he

/-- The factor alternatives give a 2-group inner intersection when an
outer five-actor survives. The PSL₂(16) alternative is perfect. -/
theorem source_first_inner_intersection_isTwoGroup
    (C : Type*) [Group C] [Group.IsSolvable (MulAut.Outer C)]
    (f : d.K1 →* MulAut C)
    (ho : 5 ∣ Nat.card (((QuotientGroup.mk' (MulAut.innerSubgroup C)).comp f).range)) :
    IsPGroup 2 (f.range ⊓ MulAut.innerSubgroup C : Subgroup _) := by
  rcases d.models with hm | hm
  · obtain ⟨e⟩ := hm.2.2.1
    have hc : Nat.card (d.K1 ⧸ pCore 2 d.K1) = 5 := by
      rw [Nat.card_congr e.toEquiv]
      simp
    exact MulAut.inner_intersection_isPGroup_of_outer_range f (by decide) hc ho
  · let : Group.IsPerfect (d.K1.subgroupOf Mc) := hm.1.perfect
    let : Group.IsPerfect d.K1 := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe d.first_le).toMonoidHom)
      (subgroupOfEquivOfLe d.first_le).surjective
    let g := (QuotientGroup.mk' (MulAut.innerSubgroup C)).comp f
    let : Group.IsPerfect g.range := Group.IsPerfect.range g
    have hb : g.range = ⊥ := by
      by_contra hh
      let : Nontrivial g.range := (nontrivial_iff_ne_bot _).mpr hh
      exact Group.IsPerfect.not_isSolvable g.range inferInstance
    change 5 ∣ Nat.card g.range at ho
    rw [hb,Subgroup.card_bot] at ho
    norm_num at ho

private theorem source_rank_zero_outer_actor
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G))
    (hr : primeRank 5 j.J = 0) :
    ∃ k : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G),
      (k : G) ∈ d.K1 ∧
      starComponentAction j.J (Mc.pCoreIn 2) k ∉
        MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J) ∧
      orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J))
        (starComponentAction j.J (Mc.pCoreIn 2) k)) = 5 := by
  obtain ⟨k,hk,_,_,_,hnot,hq⟩ :=
    source_component_star_outer_quintic_of_rank_zero s d j hn hr
  exact ⟨k,hk,hnot,hq⟩

private theorem source_natural_outer_actor
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G))
    (row : NaturalStarRow j.J (Mc.pCoreIn 2)) :
    ∃ k : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G),
      (k : G) ∈ d.K1 ∧
      starComponentAction j.J (Mc.pCoreIn 2) k ∉
        MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J) ∧
      orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J))
        (starComponentAction j.J (Mc.pCoreIn 2) k)) = 5 := by
  by_cases hr : primeRank 5 j.J = 1
  · obtain ⟨k,hk,_,_,_,hnot,hq⟩ := source_natural_row_outer_quintic s d j hr row
    exact ⟨k,hk,hnot,hq⟩
  · have hz : primeRank 5 j.J = 0 := by have := j.quintic_rank; omega
    exact source_rank_zero_outer_actor s d j hn hz

private theorem source_natural_actors_inner
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G))
    (row : NaturalStarRow j.J (Mc.pCoreIn 2))
    (ho : 5 ∣ Nat.card (((QuotientGroup.mk'
      (MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J))).comp
        ((starComponentAction j.J (Mc.pCoreIn 2)).comp
          (inclusion (source_first_le_common_normalizer s d j)))).range)) :
    ((starComponentAction j.J (Mc.pCoreIn 2)).comp
      (inclusion (source_first_le_common_normalizer s d j))).range ≤
        MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J) := by
  let C := starImage j.J (Mc.pCoreIn 2) j.J
  let N := normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G)
  let f : d.K1 →* MulAut C := (starComponentAction j.J (Mc.pCoreIn 2)).comp
    (inclusion (source_first_le_common_normalizer s d j))
  have hfr : f.range = (d.K1.subgroupOf N).map
      (starComponentAction j.J (Mc.pCoreIn 2)) := by
    rw [MonoidHom.range_comp,inclusion_range]
  let e : C ≃* SL(2,row.field.Carrier) :=
    (subgroupOfEquivOfLe row.included).symm.trans row.natural.groupEquiv
  let : Group.IsSolvable (MulAut.Outer C) :=
    Theory.PSL2.binary_outer_isSolvable_of_mulEquiv row.field.Carrier
      (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL)
  have hi2 := source_first_inner_intersection_isTwoGroup (s := s) d C f ho
  let hi := source_component_normalized_input s d j hn
  obtain ⟨S,hS⟩ := (row.geometry hi).1
  have hA : f.range ≤ (starComponentAction j.J (Mc.pCoreIn 2)).range := by
    rintro α ⟨x,rfl⟩
    exact ⟨inclusion (source_first_le_common_normalizer s d j) x,rfl⟩
  have hB : ((starM j.J (Mc.pCoreIn 2)
      (Mc ⊓ normalizer (d.K2 : Set G))).subgroupOf C).map MulAut.conj ≤
      normalizer (f.range : Set _) := by
    rw [hfr]
    exact source_borel_normalizes_first_actor s d j hi.normalizes
  let : (j.J.subgroupOf (j.J ⊔ Mc.pCoreIn 2)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le j.J.le_normalizer hn)
  have hB' : ((starM j.J (Mc.pCoreIn 2)
      ((Mc ⊓ normalizer (d.K2 : Set G)) ⊓ (j.J ⊔ Mc.pCoreIn 2))).subgroupOf C).map
      MulAut.conj ≤ normalizer (f.range : Set _) := by
    simpa only [starM_inter_join] using hB
  exact ChapterC.C27Source.rankOne_borel_actors_inner (source_join_input hi)
    row.field e S hS f.range hA hB' hi2

/-- Both original factor models are excluded on the natural row.
No ordinary-centralizer residual identity or innerness premise is used. -/
theorem source_false_of_natural_row
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G))
    (row : NaturalStarRow j.J (Mc.pCoreIn 2)) : False := by
  obtain ⟨k,hk,hnot,hq⟩ := source_natural_outer_actor s d j hn row
  let C := starImage j.J (Mc.pCoreIn 2) j.J
  let f : d.K1 →* MulAut C := (starComponentAction j.J (Mc.pCoreIn 2)).comp
    (inclusion (source_first_le_common_normalizer s d j))
  let y : d.K1 := ⟨k,hk⟩
  have he : f y = starComponentAction j.J (Mc.pCoreIn 2) k := rfl
  let q := QuotientGroup.mk' (MulAut.innerSubgroup C)
  let g := q.comp f
  have hmem : q (starComponentAction j.J (Mc.pCoreIn 2) k) ∈ g.range :=
    ⟨y,congrArg q he⟩
  have ho : orderOf (⟨q (starComponentAction j.J (Mc.pCoreIn 2) k),hmem⟩ : g.range) = 5 :=
    (Subgroup.orderOf_coe _).symm.trans hq
  have hd : 5 ∣ Nat.card g.range := ho ▸ orderOf_dvd_natCard
    (⟨q (starComponentAction j.J (Mc.pCoreIn 2) k),hmem⟩ : g.range)
  have hin := source_natural_actors_inner s d j hn row hd
  exact hnot (hin ⟨y,he⟩)

/-- Relative rank-one normality supplies the required radical normalization. -/
theorem source_false_of_rank_one_natural_row
    (hr : primeRank 5 j.J = 1) (row : NaturalStarRow j.J (Mc.pCoreIn 2)) : False :=
  source_false_of_natural_row s d j
    (source_component_rank_one_input s d j hr).normalizes row

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
