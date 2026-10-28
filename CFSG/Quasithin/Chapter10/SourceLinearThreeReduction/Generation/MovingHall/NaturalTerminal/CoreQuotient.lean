module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.CommonComponent
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CommonSylowCoreSeparation
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank

/-!
# The original natural block embeds in the common component quotient

If the comparison block had the original block's core, it would normalize
one summand of the original full module and centralize the other. Maximal
two-locality would then put it in M, contradicting its escape. Their cores
are therefore different. The shared-Sylow intersection theorem makes the
common component's two-core disjoint from the original block. Its natural
module survives the literal quotient, giving two-rank at least 2n and
excluding the noncentral-Fitting alternatives of A.3.6.

The constructor proves these conclusions under the retained natural marking
and original Hall placement. The source Hall consumer uses them in its
remaining recognition step; qt-d-10-nona5-moving-hall-three still owns
SL₃/PSL₃ recognition, natural marking and Hall placement.
Source: Aschbacher–Smith 10.2.3(4), printed p.747, and A.3.6.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterC ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem center_eq_bot_transport {X Y : Type*} [Group X] [Group Y]
    (a : X ≃* Y) (h : center X = ⊥) : center Y = ⊥ := by
  apply bot_unique
  intro y hy
  have hh := (centerCongr a.symm ⟨y,hy⟩).property
  change a.symm y ∈ center X at hh
  rw [h,mem_bot] at hh
  exact mem_bot.mpr (a.symm.injective (hh.trans a.symm.map_one.symm))

private theorem core_eq_transport {X Y : Type*} [Group X] [Group Y]
    (a : X ≃* Y) (h : pCore 2 X = blockU X) : pCore 2 Y = blockU Y := by
  rw [←pCore_map_iso 2 a,h,blockU,map_commutator,pCore_map_iso,
    map_top_of_surjective _ a.surjective,blockU]


/-- The full original module determines its maximal two-local normalizer. -/
private theorem full_module_normalizer_le :
    normalizer (D.fullModule : Set G) ≤ D.maximalLocal := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hne : D.fullModule ≠ ⊥ := by
    intro he
    exact D.module_ne_bot (bot_unique (he ▸ le_componentOrbit D.moduleSubgroup D.maximalLocal))
  exact hu.normalizer_maximal.2
    ⟨D.fullModule,hne,(D.fullModule_elementary hu).isPGroup,rfl⟩
    D.maximalLocal_normalizes_fullModule

/-- Sharing the original core would make the escaping block normalize the
whole original module, since its complementary summand is centralized. -/
theorem CommonOvercomponent.layers_ne_of_module
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (U : Subgroup G)
    (hfull : D.fullModule = (blockU c.original).map c.original.subtype ⊔ U)
    (hUS : U ≤ ⁅baumann (T : Subgroup G),c.axis⁆)
    (hout : ¬ c.comparison.map H.subtype ≤ D.maximalLocal) :
    (blockU c.original).map c.original.subtype ≠
      (blockU (c.comparison.map H.subtype)).map (c.comparison.map H.subtype).subtype := by
  intro he
  let K := c.comparison.map H.subtype
  have hKU : K ≤ normalizer (((blockU c.original).map c.original.subtype) : Set G) := by
    rw [he]
    exact K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hKC : K ≤ centralizer (U : Set G) :=
    (c.comparison_le.trans c.centralizes).trans (centralizer_le (hUS.trans le_sup_left))
  have hKV : K ≤ normalizer (D.fullModule : Set G) := by
    rw [hfull]
    exact (le_inf hKU (hKC.trans (centralizer_le_normalizer U))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact hout (hKV.trans (full_module_normalizer_le D))

/-- The actual common component has distinct natural cores, without an
additional normalizer-control premise. -/
theorem Context.common_overcomponent_separated
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    ∃ c : CommonOvercomponent T L H B n,
      (blockU c.original).map c.original.subtype ≠
        (blockU (c.comparison.map H.subtype)).map (c.comparison.map H.subtype).subtype := by
  obtain ⟨c,U,hfull,hUS,hout⟩ := ctx.common_overcomponent_with_module D n hn hF e mark hBB
  exact ⟨c,c.layers_ne_of_module D U hfull hUS hout⟩

/-- The actual quotient by the common component's two-core is faithful on
the original natural block. The common Sylow need not be Sylow in the component. -/
theorem CommonOvercomponent.quotient_injective_of_layers_ne
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n)
    (hne : (blockU c.original).map c.original.subtype ≠
      (blockU (c.comparison.map H.subtype)).map (c.comparison.map H.subtype).subtype) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le)) := by
  let C := c.overcomponent
  let J := c.original
  let K := c.comparison.map H.subtype
  let Q := (pCore 2 C).map C.subtype
  let a := c.comparison.equivMapOfInjective H.subtype H.subtype_injective
  have hK : IsShort K := RankOne.Solvable.isShort_of_equiv a c.comparison_natural.2.1
  have hcK : pCore 2 K = blockU K := core_eq_transport a c.comparison_core
  have hzK : center K = ⊥ := center_eq_bot_transport a c.comparison_center
  have hCQ : C ≤ normalizer (Q : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hinf : Q ⊓ J = ⊥ := short_pair_twoGroup_intersection_eq_bot J K
    ⁅baumann (T : Subgroup G),(B ⊓ c.comparison).map H.subtype⁆ Q
    c.original_natural.2.1 hK (pCore_isPGroup.map C.subtype)
    (c.original_lt.le.trans hCQ) (c.comparison_le.trans hCQ)
    c.original_center hzK c.original_core hcK
    c.common_sylow_original c.common_sylow_comparison hne
  let f := (QuotientGroup.mk' (pCore 2 C)).comp (inclusion c.original_lt.le)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  have hq : inclusion c.original_lt.le x ∈ pCore 2 C :=
    (QuotientGroup.eq_one_iff _).mp (show f x = 1 from hx)
  have he : (x : G) ∈ Q ⊓ J := ⟨mem_map_of_mem C.subtype hq,x.property⟩
  have hx1 : (x : G) = 1 := by simpa only [hinf,mem_bot] using he
  exact mem_bot.mpr (Subtype.ext hx1)

/-- The original natural module survives in the literal two-core quotient,
which is consequently quasisimple by the noncentral-Fitting rank exclusion. -/
theorem CommonOvercomponent.quotient_rank_and_quasisimple
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le))) :
    2*n ≤ primeRank 2 (c.overcomponent ⧸ pCore 2 c.overcomponent) ∧
      IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent) := by
  let C := c.overcomponent
  let Q := C ⧸ pCore 2 C
  have hsq : IsSQTK KnownSimple.IsKnownSimple C := ⟨
    c.local_sqtk.stronglyQuasithin.of_injective (inclusion c.component.1)
      (inclusion_injective c.component.1),
    c.local_sqtk.isKGroup.of_injective (inclusion c.component.1)
      (inclusion_injective c.component.1)⟩
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  have hC : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using c.component.2.subgroupOf_of_le le_rfl c.component.1
  let := pCore_isNilpotent (p := 2) (G := C)
  have htop : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      hC.map_quotient (pCore 2 C)
  have hU : Nat.card (blockU c.original) = 2^(2*n) := by
    rw [card_eq_card_quotient_mul_card_subgroup (blockFixed c.original),
      c.original_natural.module_card]
    have hb : blockFixed c.original = ⊥ := by
      change (center c.original).subgroupOf (blockU c.original) = ⊥
      rw [c.original_center,bot_subgroupOf]
    rw [hb,card_bot,mul_one,Nat.mul_comm n 2]
  have h2 : 2*n ≤ primeRank 2 c.original := by
    let := c.original_natural.2.1.elementary
    exact IsElementaryAbelian.primeRank_ge_of_card (blockU c.original) hU
  have hr : 2*n ≤ primeRank 2 Q := h2.trans
    (Theory.GroupTheory.primeRank_le_of_injective 2 _ hi)
  have hrank : 2 ≤ primeRank 2 (⊤ : Subgroup Q) := by
    rw [primeRank_equiv 2 (topEquiv (G := Q))]
    have hn := c.original_natural.1
    omega
  let : IsQuasisimple (⊤ : Subgroup Q) :=
    NoncentralFitting.quasisimple_of_two_le_two_rank hQ
      (pCore_quotient_pCore_eq_bot 2) htop hrank
  exact ⟨hr,IsQuasisimple.of_mulEquiv (topEquiv (G := Q))⟩

/-- The source constructor supplies a faithful original block inside the
quasisimple two-core quotient, including the full original module rank. -/
theorem Context.common_overcomponent_faithful
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    ∃ c : CommonOvercomponent T L H B n,
      Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
        (inclusion c.original_lt.le)) ∧
      2*n ≤ primeRank 2 (c.overcomponent ⧸ pCore 2 c.overcomponent) ∧
      IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent) := by
  obtain ⟨c,hne⟩ := ctx.common_overcomponent_separated D n hn hF e mark hBB
  have hi := c.quotient_injective_of_layers_ne hne
  exact ⟨c,hi,c.quotient_rank_and_quasisimple hi⟩

end CFSG.Quasithin.Chapter10.MovingHall
