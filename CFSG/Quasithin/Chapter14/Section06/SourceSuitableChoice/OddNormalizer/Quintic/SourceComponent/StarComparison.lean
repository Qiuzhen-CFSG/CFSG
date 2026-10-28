module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.CoreStarNormalizerAction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.OuterComparison.KernelGenerators

/-!
# Marked star actions for the source escaping component

The original K₁ acts on the actual C.2.7 star image. Equivariance of the
core-to-star cover retains the order-five generator, its innerness, and its
outer order. The original intersection B normalizes the image of K₁ in
this automorphism group. At rank one, the kernel calculation gives either
K₁ ≤ J K₂ or a genuine outer five-actor on that same star image.

These statements apply to SourceEscapingComponent, without the legacy
ordinary-centralizer residual identity. The source assembly owner
qt-e-14615-quintic-exclusion still constructs NormalizerGeometry and
proves the marked model comparisons. The earlier 14.6.12--14 inputs remain
with qt-e-suitable-odd-normalizer. This module does not assert p = 3.

Source: Aschbacher--Smith 14.6.15, printed p.1035, and C.2.7, pp.145--147.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction
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

include j in
/-- The original first factor acts on both groups defining the star quotient. -/
theorem source_first_le_common_normalizer :
    d.K1 ≤ normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) := by
  refine le_inf ?_ ?_
  · exact (show d.K1 ≤ residualClosure H Mc from d.join_eq ▸ le_sup_left).trans
      j.normalized_by_closure
  · exact d.first_le.trans (Mc.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc)))

/-- The C.2.7 input when the radical fixes the component, independently of containment. -/
theorem source_component_normalized_input
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G)) :
    Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G)) (Mc.pCoreIn 2)
      (Mc ⊓ normalizer (d.K2 : Set G)) j.J := by
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  exact ⟨hs,⟨j.component_le,j.component⟩,j.quasisimple,
    j.characteristic_component,j.outside,hn⟩

/-- At rank one relative normality supplies the same original input. -/
theorem source_component_rank_one_input (hr : primeRank 5 j.J = 1) :
    Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G)) (Mc.pCoreIn 2)
      (Mc ⊓ normalizer (d.K2 : Set G)) j.J := by
  let := j.rank_one_normal hr
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  exact source_component_normalized_input s d j
    (hs.radical_le.trans (le_normalizer_of_normal_subgroupOf j.component_le))

/-- An order-five actor survives on the literal C.2.7 star image. -/
theorem source_component_star_quintic
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G)) :
    ∃ k : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G),
      (k : G) ∈ d.K1 ∧ orderOf k = 5 ∧
      orderOf (starComponentAction j.J (Mc.pCoreIn 2) k) = 5 := by
  obtain ⟨k,hk,ho,ha⟩ := exists_first_generator_with_quotient_order s d j.J
    j.component_le j.component j.quasisimple j.outside
  let l : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G) :=
    ⟨k,source_first_le_common_normalizer s d j hk⟩
  refine ⟨l,hk,?_,?_⟩
  · exact (Subgroup.orderOf_coe l).symm.trans ((Subgroup.orderOf_coe k).trans ho)
  · rw [starComponentAction_order (source_component_normalized_input s d j hn)]
    exact ha

/-- At rank zero the same actor is outer on the actual star image. -/
theorem source_component_star_outer_quintic_of_rank_zero
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G)) (hr : primeRank 5 j.J = 0) :
    ∃ k : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G),
      (k : G) ∈ d.K1 ∧ (k : G) ∉ j.J ∧ orderOf k = 5 ∧
      orderOf (starComponentAction j.J (Mc.pCoreIn 2) k) = 5 ∧
      starComponentAction j.J (Mc.pCoreIn 2) k ∉
        MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J) ∧
      orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J))
        (starComponentAction j.J (Mc.pCoreIn 2) k)) = 5 := by
  obtain ⟨k,hk,hout,ho,ha,hi,hoq⟩ := source_component_outer_quintic_of_rank_zero s d j hr
  let l : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G) :=
    ⟨k,source_first_le_common_normalizer s d j hk⟩
  have h := source_component_normalized_input s d j hn
  refine ⟨l,hk,hout,?_,?_,?_,?_⟩
  · exact (Subgroup.orderOf_coe l).symm.trans ((Subgroup.orderOf_coe k).trans ho)
  · rw [starComponentAction_order h]
    exact ha
  · exact fun hh => hi ((starComponentAction_inner_iff h l).mp hh)
  · rw [starComponentAction_outer_order h]
    exact hoq

/-- A no-five outer-group calculation for the actual star model forces rank one. -/
theorem source_component_rank_one_of_star_outer_card
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G))
    (ho : ¬5 ∣ Nat.card (MulAut.Outer (starImage j.J (Mc.pCoreIn 2) j.J))) :
    primeRank 5 j.J = 1 := by
  have hr := j.quintic_rank
  have hzero : primeRank 5 j.J ≠ 0 := by
    intro hz
    obtain ⟨k,_,_,_,_,_,hk⟩ := source_component_star_outer_quintic_of_rank_zero s d j hn hz
    exact ho (hk ▸ orderOf_dvd_natCard
      (QuotientGroup.mk' (MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J))
        (starComponentAction j.J (Mc.pCoreIn 2) k)))
  omega
/-- The actual source intersection normalizes the image of K₁ in the
star automorphism group. Its own action is the inner action of its literal
star image. This retains the marked subgroup needed by the model comparison. -/
theorem source_intersection_star_normalizes_first
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G)) :
    let B := conjugateSpanBy j.J (Mc.pCoreIn 2) ⊓ (Mc ⊓ normalizer (d.K2 : Set G))
    let N := normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G)
    (((B.subgroupOf j.J).map (toStarImage j.J (Mc.pCoreIn 2))).map
      (MulAut.conj : starImage j.J (Mc.pCoreIn 2) j.J →* _)) ≤
      normalizer (((d.K1.subgroupOf N).map
        (starComponentAction j.J (Mc.pCoreIn 2))) : Set _) := by
  let B := conjugateSpanBy j.J (Mc.pCoreIn 2) ⊓ (Mc ⊓ normalizer (d.K2 : Set G))
  let N := normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G)
  let f := starComponentAction j.J (Mc.pCoreIn 2)
  have hBJ : B ≤ j.J := inf_le_left.trans (conjugateSpanBy_le le_rfl hn)
  have hBN : B ≤ N := le_inf (hBJ.trans j.J.le_normalizer)
    ((inf_le_right.trans inf_le_left : B ≤ Mc).trans
      (Mc.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))))
  have hBK : B.subgroupOf N ≤ normalizer (d.K1.subgroupOf N : Set N) :=
    (comap_mono j.intersection_normalizes_first).trans (le_normalizer_comap N.subtype)
  have him := (map_mono (f := f) hBK).trans (le_normalizer_map f)
  change (((B.subgroupOf j.J).map (toStarImage j.J (Mc.pCoreIn 2))).map
    (MulAut.conj : starImage j.J (Mc.pCoreIn 2) j.J →* _)) ≤
      normalizer ((d.K1.subgroupOf N).map f : Set _)
  rintro α ⟨y,⟨x,hx,rfl⟩,rfl⟩
  apply him
  refine ⟨⟨x,hBN hx⟩,hx,?_⟩
  exact starComponentAction_on_component j.J (Mc.pCoreIn 2) _ x.property

/-- No five-rank is lost in the star component used by C.2.7. -/
theorem source_component_star_five_rank
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G)) :
    primeRank 5 (starImage j.J (Mc.pCoreIn 2) j.J) = primeRank 5 j.J :=
  starImage_five_rank_from_source (source_component_normalized_input s d j hn)

/-- The rank-one source branch supplies the model rank, the nontrivial
quintic actor, and its exact innerness detector without assuming K₁ ≤ J. -/
theorem source_component_rank_one_star_comparison (hr : primeRank 5 j.J = 1) :
    primeRank 5 (starImage j.J (Mc.pCoreIn 2) j.J) = 1 ∧
    ∃ k : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G),
      (k : G) ∈ d.K1 ∧ orderOf k = 5 ∧
      orderOf (starComponentAction j.J (Mc.pCoreIn 2) k) = 5 ∧
      (starComponentAction j.J (Mc.pCoreIn 2) k ∈
          MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J) ↔
        pCoreNormalizerAction 2 j.J (inclusion inf_le_left k) ∈
          MulAut.innerSubgroup (j.J ⧸ pCore 2 j.J)) := by
  have h := source_component_rank_one_input s d j hr
  obtain ⟨k,hk,ho,ha⟩ := source_component_star_quintic s d j h.normalizes
  exact ⟨(starImage_five_rank_from_source h).trans hr,
    k,hk,ho,ha,starComponentAction_inner_iff h k⟩

/-- Apply the proved kernel identification to the same source component.
The displayed homomorphism is the conjugation action of the literal second
normalizer on J/O₂(J). -/
theorem source_component_rank_one_kernel_five_closure (hr : primeRank 5 j.J = 1) :
    ∃ hn : normalizer (d.K2 : Set G) ≤ normalizer (j.J : Set G),
      closure {x : G | x ∈
        (((pCoreNormalizerAction 2 j.J).comp (inclusion hn)).ker).map
          (normalizer (d.K2 : Set G)).subtype ∧ orderOf x = 5} = d.K2 :=
  component_rank_one_literal_kernel_five_closure s d j.J j.component_le j.component
    j.quasisimple j.outside j.characteristic_component hr

/-- Apply the literal rank-one kernel argument to the same source component.
The outer alternative is transported through the actual central cover, so
it concerns the C.2.7 star image and its marked first-factor actor. -/
theorem source_component_rank_one_first_join_or_star_outer
    (hr : primeRank 5 j.J = 1) :
    d.K1 ≤ j.J ⊔ d.K2 ∨
    ∃ k : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G),
      (k : G) ∈ d.K1 ∧ (k : G) ∉ j.J ⊔ d.K2 ∧ orderOf k = 5 ∧
      orderOf (starComponentAction j.J (Mc.pCoreIn 2) k) = 5 ∧
      starComponentAction j.J (Mc.pCoreIn 2) k ∉
        MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J) ∧
      orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J))
        (starComponentAction j.J (Mc.pCoreIn 2) k)) = 5 := by
  rcases component_rank_one_first_join_or_outer s d j.J j.component_le j.component
      j.quasisimple j.outside j.characteristic_component hr with hle | ⟨k,hk,he,ho,ha,hi,hq⟩
  · exact Or.inl hle
  right
  let l : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G) :=
    ⟨k,source_first_le_common_normalizer s d j hk⟩
  have h := source_component_rank_one_input s d j hr
  refine ⟨l,hk,he,?_,?_,?_,?_⟩
  · exact (Subgroup.orderOf_coe l).symm.trans ((Subgroup.orderOf_coe k).trans ho)
  · rw [starComponentAction_order h]
    exact ha
  · exact fun hh => hi ((starComponentAction_inner_iff h l).mp hh)
  · rw [starComponentAction_outer_order h]
    exact hq

/-- A prime-to-five outer-group calculation eliminates the actual outer
alternative. The surviving conclusion is K₁ ≤ J K₂, without silently
strengthening it to K₁ ≤ J. The remaining model comparison is owned by
qt-e-14615-quintic-exclusion. -/
theorem source_component_first_le_join_of_star_outer_card
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G))
    (ho : ¬5 ∣ Nat.card (MulAut.Outer (starImage j.J (Mc.pCoreIn 2) j.J))) :
    primeRank 5 j.J = 1 ∧ d.K1 ≤ j.J ⊔ d.K2 := by
  have hr := source_component_rank_one_of_star_outer_card s d j hn ho
  refine ⟨hr,?_⟩
  rcases source_component_rank_one_first_join_or_star_outer s d j hr with hle | ⟨k,_,_,_,_,_,hk⟩
  · exact hle
  · exact (ho (hk ▸ orderOf_dvd_natCard
      (QuotientGroup.mk' (MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J))
        (starComponentAction j.J (Mc.pCoreIn 2) k)))).elim

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
