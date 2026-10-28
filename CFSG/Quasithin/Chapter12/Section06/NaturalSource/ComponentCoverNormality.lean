module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentCoverPlacement
public import Theory.GroupTheory.GeneralizedFitting.ComponentSmallCenterNormal
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The full ambient action in the two surviving cubic-cover cases

The original H-star has three-rank at most two. Its selected component
with cubic center has rank two, so the commuting-component argument
makes it normal in H-star. Normality reflects through the original
two-core quotient to the C-component K in H.

Conjugation now extends the existing marked KL1V action to all of H,
with its exact centralizer kernel and the actual original Sylow image.
The refined source catalogue retains the same K, residual placement,
inner action, earlier geometry and two surviving cover alternatives.
The model normalizer and module exclusions, abelian point span and
universal natural reduction remain further obligations.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Rank saturation makes the selected cubic-centered component normal in
all of the original H-star, and reflects normality to its original C-component. -/
theorem SourceHypothesis.original_cubicCenter_component_normal
    (hz : z ≠ 1) {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H)
    (hc : Nat.card (center (Nonabelian.Setup.star H c.K)) = 3) :
    (Nonabelian.Setup.star H c.K).Normal ∧ (c.K.subgroupOf H).Normal := by
  let B := Nonabelian.Setup.star H c.K
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
  have hn := c.component.normal_of_rank_two_small_center
    (S.original_star_three_rank D hZ z hz hH) hr (by rw [hc]; decide)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  exact ⟨hn,cComponent_normal_of_quotient_normal c.ccomponent (pCore 2 H) hn⟩

/-- In both remaining cover rows, the full original H normalizes K.
This includes the original T and R1 without replacing either subgroup. -/
theorem SourceHypothesis.original_cubicCover_component_normal
    (hz : z ≠ 1) {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7 ∨
      Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K)) :
    (Nonabelian.Setup.star H c.K).Normal ∧ H ≤ normalizer (c.K : Set G) := by
  have hc : Nat.card (center (Nonabelian.Setup.star H c.K)) = 3 := by
    rcases hm with ⟨_,⟨e⟩,_⟩|⟨_,⟨e⟩,_⟩ <;> rw [Nat.card_congr e.toEquiv] <;> simp
  obtain ⟨hb,hk⟩ := S.original_cubicCenter_component_normal D hZ z hz hH c hc
  let := hk
  refine ⟨hb,?_⟩
  intro x hx
  have hn : (⟨x,hx⟩ : H) ∈ normalizer (c.K.subgroupOf H : Set H) :=
    le_normalizer_of_normal (mem_top _)
  rwa [←subgroupOf_normalizer_eq c.le_H] at hn

/-- Extend the literal marked KL1V action to H. Its kernel remains the
full preimage of the component centralizer, and the original T maps to
an actual Sylow subgroup of the action image. -/
theorem SourceHypothesis.original_cubicCover_full_action
    (hz : z ≠ 1) {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7 ∨
      Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K)) :
    ∃ f : H →* MulAut (Nonabelian.Setup.star H c.K),
      (∀ (x : H) (k : Nonabelian.Setup.star H c.K),
        (f x k : Nonabelian.Setup.Hstar H) =
          QuotientGroup.mk' (pCore 2 H) x * k.val *
            (QuotientGroup.mk' (pCore 2 H) x)⁻¹) ∧
      f.ker = (centralizer (Nonabelian.Setup.star H c.K : Set (Nonabelian.Setup.Hstar H))).comap
        (QuotientGroup.mk' (pCore 2 H)) ∧
      f.comp (inclusion a.local_le) = a.action ∧
      (c.K.subgroupOf H).map f = MulAut.innerSubgroup (Nonabelian.Setup.star H c.K) ∧
      ∃ P : Sylow 2 f.range,
        (P : Subgroup f.range).map f.range.subtype = ((T : Subgroup G).subgroupOf H).map f := by
  let B := Nonabelian.Setup.star H c.K
  let := (S.original_cubicCover_component_normal D hZ z hz hH c hm).1
  let q := QuotientGroup.mk' (pCore 2 H)
  let f : H →* MulAut B := (MulAut.conjNormal : Nonabelian.Setup.Hstar H →* MulAut B).comp q
  have hf (x : H) (k : B) : (f x k : Nonabelian.Setup.Hstar H) = q x*k.val*(q x)⁻¹ := rfl
  have ha : f.comp (inclusion a.local_le) = a.action := by
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro k
    exact Subtype.ext (a.conjugation x k).symm
  refine ⟨f,hf,?_,ha,?_,?_⟩
  · change ((MulAut.conjNormal : Nonabelian.Setup.Hstar H →* MulAut B).comp q).ker = _
    rw [←MonoidHom.comap_ker,MulAut.conjNormal_ker_eq_centralizer]
  · rw [←a.component_image]
    ext t
    constructor
    · rintro ⟨x,hx,rfl⟩
      let y : c.localActor := ⟨x.val,(le_sup_left.trans le_sup_left : c.K ≤ c.localActor) hx⟩
      exact ⟨y,hx,(DFunLike.congr_fun ha y).symm⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨inclusion a.local_le x,hx,DFunLike.congr_fun ha x⟩
  · have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
    refine ⟨(T.subtype hTH).mapSurjective f.rangeRestrict_surjective,?_⟩
    rw [Sylow.coe_mapSurjective,Sylow.coe_subtype,map_map]
    rfl

/-- The source catalogue retains normality of the literal component in
both surviving nonsimple cases, together with the proved placement and
inner action of the same original residual. -/
theorem SourceHypothesis.original_selectedComponent_simple_or_normal_internal_cover
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
        a.action.range = MulAut.innerSubgroup B ∧
        B.Normal ∧ H ≤ normalizer (c.K : Set G)) := by
  rcases S.original_selectedComponent_simple_or_internal_cover D hZ z hz hTV hTz
    hbound hns hH hn c a with hs|⟨hc,hm,hA,ha⟩
  · exact Or.inl hs
  · exact Or.inr ⟨hc,hm,hA,ha,
      S.original_cubicCover_component_normal D hZ z hz hH c hm⟩

end CFSG.Quasithin.Chapter12.Section06
