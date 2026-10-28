module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentLinearFour
public import Theory.GroupTheory.PrimeRankInnerContainment
public import Theory.GroupAction.CubicCoverCenterFixer
public import Theory.Alternating.TripleSevenCubicFacts
public import Theory.Mathieu.M22.TripleCover.CubicFacts
public import Theory.GroupTheory.PResidual.NormalizedSupplement

/-!
# Placing the original point residual in the remaining cubic covers

In either the cubic A₇ or cubic M₂₂ row, the two-perfect L₁ action is inner
because the outer group is a two-group. Cubic inner automorphisms lift to
cubic elements. Rank saturation in the unchanged H/O₂(H) therefore places
every original Sylow E₉ inside K-star. The actual E₉ quotient of L₁ and
two-perfectness absorb its two-core supplement, proving L₁-star ≤ K-star.

The original V action fixes the component center, so it too is inner.
Consequently the literal KL₁V action has exactly the inner component image.
The refined source catalogue retains the genuine central quotient and
cover alternatives. The A₇ R₁-normalizer argument, M₂₂ module exclusion,
remaining simple components, abelian point span and universal natural
reduction are still required; all earlier geometry stays explicit.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section06
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

private theorem cubic_cover_sylow_star_le
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hc : Nat.card (center (Nonabelian.Setup.star H c.K)) = 3)
    (ho : IsPGroup 2 (MulAut.Outer (Nonabelian.Setup.star H c.K)))
    (h9 : ∀ x : Nonabelian.Setup.star H c.K, x ^ 9 = 1 → x ^ 3 = 1)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    Nonabelian.Setup.star H ((P : Subgroup (D.fullSetup hZ T z).L₁).map
      (D.fullSetup hZ T z).L₁.subtype) ≤ Nonabelian.Setup.star H c.K := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let A := (E.L₁.subgroupOf c.localActor).map a.action
  let := c.component.2
  have hr : primeRank 3 B = 2 := by
    apply le_antisymm
    · exact (_root_.primeRank_le_of_injective 3 B.subtype B.subtype_injective).trans
        (S.original_star_three_rank D hZ z hz hH)
    · exact two_le_primeRank_of_nontrivial_prime_center (by decide)
        (IsPGroup.of_card (p := 3) (n := 1) hc) (by
          intro he
          rw [he,card_bot] at hc
          omega)
  have hi : A ≤ MulAut.innerSubgroup B := by
    have he := a.residual_twoPerfect.hom_eq_one_of_isPGroup ho
      ((QuotientGroup.mk' (MulAut.innerSubgroup B)).comp A.subtype)
    intro t ht
    exact (QuotientGroup.eq_one_iff t).mp (DFunLike.congr_fun he ⟨t,ht⟩)
  have hlift (b : B) (hb : b^3 ∈ center B) : b^3=1 := by
    apply h9
    have hh := pow_card_eq_one' (x := (⟨b^3,hb⟩ : center B))
    rw [hc] at hh
    simpa only [coe_pow,coe_one,←pow_mul] using congrArg Subtype.val hh
  let j : P →* c.localActor := (inclusion (show E.L₁ ≤ c.localActor from
    le_sup_right.trans le_sup_left)).comp (P : Subgroup E.L₁).subtype
  let q := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion a.local_le)
  have hp (p : P) : q (j p) ∈ B := by
    have hn : q (j p) ∈ normalizer (B : Set (Nonabelian.Setup.Hstar H)) :=
      S.original_residual_star_normalizes_selectedComponent D hZ z hz hH c
        (mem_map_of_mem _ p.val.property)
    refine B.mem_of_prime_pow_eq_one_of_inner_action
      (S.original_star_three_rank D hZ z hz hH) hr hlift ?_ hn ?_
    · have hp3 := (S.original_point_residual_sylow D hZ z hz hTz P).1
      let := hp3
      have he : p ^ 3=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 P) p
      rw [←map_pow,←map_pow,he,map_one,map_one]
    · have he : B.normalizerMonoidHom ⟨q (j p),hn⟩ = a.residualSylowAction P p := by
        ext b
        exact (a.conjugation (j p) b).symm
      rw [he]
      exact hi ⟨j p,p.val.property,rfl⟩
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨p,hpP,he⟩ := hy
  have heH : (inclusion a.local_le (j ⟨p,hpP⟩) : H) = y := Subtype.ext he
  simpa only [q,MonoidHom.comp_apply,heH] using hp ⟨p,hpP⟩

private theorem residual_star_le_of_sylow_star_le
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁)
    (hP : Nonabelian.Setup.star H ((P : Subgroup (D.fullSetup hZ T z).L₁).map
      (D.fullSetup hZ T z).L₁.subtype) ≤ Nonabelian.Setup.star H c.K) :
    Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ ≤ Nonabelian.Setup.star H c.K := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  let f : E.L₁ →* Nonabelian.Setup.Hstar H :=
    (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hAH)
  let A := Nonabelian.Setup.star H E.L₁
  let R := (pCore 2 E.L₁).map f
  have htop : (⊤ : Subgroup E.L₁).map f = A := by
    apply le_antisymm
    · rintro x ⟨y,_,rfl⟩
      exact mem_map_of_mem _ y.property
    · rintro x ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,mem_top _,rfl⟩
  have hPA : (P : Subgroup E.L₁).map f ≤ B := by
    rintro x ⟨p,hp,rfl⟩
    exact hP (mem_map_of_mem _ (show (inclusion hAH p : G) ∈
      (P : Subgroup E.L₁).map E.L₁.subtype from mem_map_of_mem E.L₁.subtype hp))
  obtain ⟨g,_,hg,_,_,hs⟩ := S.original_point_residual_quotient D hZ z hz hTz
  obtain ⟨s,hs⟩ := hs P
  have hmap : (P : Subgroup E.L₁).map g = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨p,rfl⟩ := s.surjective x
    exact ⟨p,p.property,(hs p).symm⟩
  have hgen : (P : Subgroup E.L₁) ⊔ pCore 2 E.L₁ = ⊤ := by
    rw [←hg,←comap_map_eq,hmap,comap_top]
  have hAR : A ≤ B ⊔ R := by
    rw [←htop,←hgen,Subgroup.map_sup]
    exact sup_le_sup_right hPA R
  apply A.le_of_isPPerfect_of_le_sup_of_normalizes B R
    (S.original_point_residual_star_twoPerfect D hZ z hH) (pCore_isPGroup.map f) _ hAR
  exact (map_mono (show pCore 2 E.L₁ ≤ ⊤ from le_top)).trans
    (htop.le.trans (S.original_residual_star_normalizes_selectedComponent D hZ z hz hH c))

/-- In the cubic A₇ cover branch, the original point residual lies in the
selected component after the literal quotient H → H/O₂(H). -/
theorem SourceHypothesis.original_alternatingSevenCover_residual_star_le
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7) :
    Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ ≤ Nonabelian.Setup.star H c.K := by
  obtain ⟨_,⟨ec⟩,⟨e⟩⟩ := hm
  let := c.component.2
  have hc : Nat.card (center (Nonabelian.Setup.star H c.K))=3 := by
    rw [Nat.card_congr ec.toEquiv]; simp
  obtain ⟨j⟩ := GLS3.Chapter5.OddCentralCovers.triple_seven_equiv e hc
  have ho := GLS3.Chapter5.OddCentralCovers.tripleSeven_outer_two.of_equiv (MulAut.outerCongr j).symm
  have h9 (x : Nonabelian.Setup.star H c.K) (hx : x^9=1) : x^3=1 := by
    apply j.injective
    simpa only [map_pow,map_one] using GLS3.Chapter5.OddCentralCovers.tripleSeven_cube_eq_one_of_ninth
      (show (j x)^9=1 from by rw [←map_pow,hx,map_one])
  let P : Sylow 3 (D.fullSetup hZ T z).L₁ := default
  exact residual_star_le_of_sylow_star_le S D hZ z hz hTz hH c P
    (cubic_cover_sylow_star_le S D hZ z hz hTz hH c a hc ho h9 P)

/-- The same placement holds in the actual cubic M₂₂ cover, with both
source subgroups retained inside the unchanged H-star. -/
theorem SourceHypothesis.original_mathieuCover_residual_star_le
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K)) :
    Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ ≤ Nonabelian.Setup.star H c.K := by
  obtain ⟨_,⟨ec⟩,⟨e⟩⟩ := hm
  let := c.component.2
  have hc : Nat.card (center (Nonabelian.Setup.star H c.K))=3 := by
    rw [Nat.card_congr ec.toEquiv]; simp
  have ho : IsPGroup 2 (MulAut.Outer (Nonabelian.Setup.star H c.K)) :=
    IsPGroup.of_card_dvd_pow (n := 1) ((card_dvd_of_injective (MulAut.centralQuotientOuter e)
      (MulAut.centralQuotientOuter_injective e)).trans
        Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)
  let P : Sylow 3 (D.fullSetup hZ T z).L₁ := default
  exact residual_star_le_of_sylow_star_le S D hZ z hz hTz hH c P
    (cubic_cover_sylow_star_le S D hZ z hz hTz hH c a hc ho
      (fun _ hx => Sporadic.Mathieu.M22TripleCover.cube_eq_one_of_ninth_of_central_quotient e hc hx) P)

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- In either surviving cubic cover, the original marked V-action is inner:
its previously proved fixation of the actual center rules out outer automorphisms. -/
theorem SourceHypothesis.original_cubicCover_module_inner
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7 ∨
      Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K)) :
    (V.subgroupOf c.localActor).map a.action ≤ MulAut.innerSubgroup (Nonabelian.Setup.star H c.K) := by
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  intro t ht
  have hfix := S.original_action_component_center_fixed D hZ z hz hTV hTz hbound hH hn c a t ht
  rcases hm with ⟨_,⟨ec⟩,⟨e⟩⟩|⟨_,⟨ec⟩,⟨e⟩⟩
  · have hc : Nat.card (center B)=3 := by rw [Nat.card_congr ec.toEquiv]; simp
    exact GLS3.Chapter5.OddCentralCovers.inner_of_fixes_center e hc t hfix
  · have hc : Nat.card (center B)=3 := by rw [Nat.card_congr ec.toEquiv]; simp
    exact Sporadic.Mathieu.M22TripleCover.inner_of_fixes_center_of_quotient e hc t hfix

/-- The entire literal KL₁V action has exactly the inner image in either
surviving cubic-cover row. In particular X-hat equals K-hat under the original action. -/
theorem SourceHypothesis.original_cubicCover_action_range_inner
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7 ∨
      Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K)) :
    a.action.range = MulAut.innerSubgroup (Nonabelian.Setup.star H c.K) := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  have hA : Nonabelian.Setup.star H E.L₁ ≤ B := by
    rcases hm with h7|h22
    · exact S.original_alternatingSevenCover_residual_star_le D hZ z hz hTz hH c a h7
    · exact S.original_mathieuCover_residual_star_le D hZ z hz hTz hH c a h22
  have hi : (E.L₁.subgroupOf c.localActor).map a.action ≤ MulAut.innerSubgroup B := by
    rintro t ⟨x,hx,rfl⟩
    let b : B := ⟨QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le x),
      hA (mem_map_of_mem _ hx)⟩
    refine ⟨b,?_⟩
    ext k
    exact (a.conjugation x k).symm
  have hU := S.original_cubicCover_module_inner D hZ z hz hTV hTz hbound hH hn c a hm
  have hKX : c.K ≤ c.localActor := le_sup_left.trans le_sup_left
  have hAX : E.L₁ ≤ c.localActor := le_sup_right.trans le_sup_left
  have hVX : V ≤ c.localActor := le_sup_right
  have hgen : c.K.subgroupOf c.localActor ⊔ E.L₁.subgroupOf c.localActor ⊔
      V.subgroupOf c.localActor = ⊤ := by
    rw [←subgroupOf_sup hKX hAX,←subgroupOf_sup (sup_le hKX hAX) hVX]
    exact subgroupOf_self _
  apply le_antisymm
  · rw [MonoidHom.range_eq_map,←hgen,Subgroup.map_sup,Subgroup.map_sup,a.component_image]
    exact sup_le (sup_le le_rfl hi) hU
  · rw [←a.component_image]
    exact map_le_range _ _

/-- The original catalogue now includes actual residual placement and inner
faithful-action equality for every nonsimple selected component. The A₇ and
M₂₂ exclusions themselves remain subsequent source obligations. -/
theorem SourceHypothesis.original_selectedComponent_simple_or_internal_cover
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    let B := Nonabelian.Setup.star H c.K
    IsSimpleGroup B ∨
      (Nonempty (center B ≃* Multiplicative (ZMod 3)) ∧
        (Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
          Chapter1.Section02.LocalModels.IsM22Cover B) ∧
        Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ ≤ B ∧
        a.action.range = MulAut.innerSubgroup B) := by
  rcases S.original_selectedComponent_simple_or_alternating_mathieu_cover D hZ z hz hTV hTz
    hbound hns hH hn c a with hs|⟨hc,hm⟩
  · exact Or.inl hs
  · refine Or.inr ⟨hc,hm,?_,S.original_cubicCover_action_range_inner D hZ z hz hTV hTz hbound hH hn c a hm⟩
    rcases hm with h7|h22
    · exact S.original_alternatingSevenCover_residual_star_le D hZ z hz hTz hH c a h7
    · exact S.original_mathieuCover_residual_star_le D hZ z hz hTz hH c a h22

end CFSG.Quasithin.Chapter12.Section06
