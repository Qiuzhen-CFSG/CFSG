module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.ComparisonAction
public import Theory.GroupTheory.CComponent.QuasisimpleImageRigidity
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.RankTwoComparison

/-!
# Original Hall placement from the containing action

Equal nontrivial comparison images recover equality upstairs whenever
the original containing two-core quotient is quasisimple. Otherwise,
a rank-two action image gives a central cover from that original quotient.
Solvable Sylow control and the pair of local components lift through
this cover, giving Borel normalization and placement of the original Hall.
The action kernel is not asserted to equal the original two-core.

Thus a proper single comparison either gives original Hall placement or
has a nonquasisimple containing two-core quotient or an actual small
A₇, SL₄(2), or SL₅(2) action image. MovingHall.Source consumes this reduction;
qt-d-10-nona5-moving-hall-three retains the remaining source branches.
Source: Aschbacher–Smith 10.2.3, printed p.746, cases (b)–(d).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- Equal actual action images force equality of the original comparison subgroups. -/
theorem ComparisonConfiguration.single_eq_of_action_image_eq
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    (hqs : IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent))
    (heq : letI := (c.orbit_reduced D).normal
      ((c.component.map H.subtype).subgroupOf (c.join D)).map (actionMk (c.orbit D)) =
        (c.overcomponent.subgroupOf (c.join D)).map (actionMk (c.orbit D))) :
    c.component.map H.subtype = c.overcomponent := by
  let J := c.join D
  let I := c.overcomponent.subgroupOf J
  let K := (c.component.map H.subtype).subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let := (c.orbit_reduced D).normal
  let q := actionMk (c.orbit D)
  let i : I ≃* c.overcomponent := subgroupOfEquivOfLe le_sup_left
  let iq := QuotientGroup.congr (pCore 2 I) (pCore 2 c.overcomponent) i (pCore_map_iso 2 i)
  let := hqs
  let : IsQuasisimple (I ⧸ pCore 2 I) := IsQuasisimple.of_mulEquiv iq.symm
  have hI : I.IsCComponent := (c.local_components D).2.1
  have hKI : K ≤ I := comap_mono c.component_le
  have hKJ : c.component.map H.subtype ≤ J := c.component_le.trans le_sup_left
  have hPK : (P : Subgroup J) ≤ normalizer (K : Set J) := by
    rw [←subgroupOf_normalizer_eq hKJ]
    exact comap_mono (c.single_normalized D hsingle)
  obtain ⟨S,hS,_⟩ := c.single_small_image_local D hsingle
  have hc : pCore 2 I ≤ (P : Subgroup J).subgroupOf I :=
    hS ▸ pCore_isPGroup.le_sylow_of_normal S
  have hn : pCore 2 I ≤ normalizer (K.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hKI]
    exact hc.trans (comap_mono hPK)
  have hne : I.map q ≠ ⊥ := fun hz => c.small_image_ne_bot D (heq.trans hz)
  have he := Theory.GroupTheory.IsCComponent.eq_of_image_eq_of_twoCore_normalizes q hI hKI heq hne hn
  have hm := congrArg (Subgroup.map J.subtype) he
  change ((c.component.map H.subtype).subgroupOf J).map J.subtype =
    (c.overcomponent.subgroupOf J).map J.subtype at hm
  simpa only [map_subgroupOf_eq_of_le hKJ,map_subgroupOf_eq_of_le
    (show c.overcomponent ≤ J from le_sup_left)] using hm

/-- A proper comparison in a quasisimple core quotient has a genuine containing-action model. -/
theorem ComparisonConfiguration.single_action_model_of_quasisimple_proper
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    (hqs : IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent))
    (hproper : c.component.map H.subtype < c.overcomponent)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    letI := (c.orbit_reduced D).normal
    PointControl.Constrained.ContainingModel
      ((c.overcomponent.subgroupOf (c.join D)).map (actionMk (c.orbit D))) := by
  exact (c.single_action_model_or_full D hsingle n hn hF e).resolve_left
    (fun he => hproper.ne (c.single_eq_of_action_image_eq D hsingle hqs he))

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open ChapterA.Section03

/-- Rank-two geometry lifts from a two-core-free action image through the actual central cover. -/
theorem comparison_geometry_of_quasisimple_core_cover
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y] [IsQuasisimple Y]
    (f : X →* Y) (hf : Function.Surjective f) (hc : pCore 2 Y = ⊥)
    (hq : IsQuasisimple (X ⧸ pCore 2 X)) (hm : ComparisonRankTwo Y) :
    SolvableSylowControl 2 (X ⧸ pCore 2 X) ∧ ∀ S : Sylow 2 (X ⧸ pCore 2 X),
      ∃ P Q : Subgroup (X ⧸ pCore 2 X), ∀ K : Subgroup (X ⧸ pCore 2 X),
        K ∈ localCComponents S → K ≠ ⊤ → K = P ∨ K = Q := by
  have hk : pCore 2 X ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    apply bot_unique
    rw [←hc]
    exact le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  let g := QuotientGroup.lift (pCore 2 X) f hk
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ _ hf _
  let := hq
  let a : Covering (X ⧸ pCore 2 X) Y := { toMonoidHom := g, surjective := hg }
  obtain ⟨hcontrol,hpair⟩ := comparison_rank_two_geometry hm
  exact ⟨SolvableSylowControl.of_surjective_central_kernel g hg a.ker_le_center hcontrol,
    local_pair_of_central_cover g hg a.ker_le_center hpair⟩

open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- An actual rank-two action image makes the original Borel normalize the original comparison. -/
theorem ComparisonConfiguration.borel_normalizes_of_single_action_rank_two
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    (hqs : IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hm : letI := (c.orbit_reduced D).normal
      ComparisonRankTwo ((c.overcomponent.subgroupOf (c.join D)).map (actionMk (c.orbit D)))) :
    sourceOrbitBorel T L ≤ normalizer (c.component.map H.subtype : Set G) := by
  let J := c.join D
  let I := c.overcomponent.subgroupOf J
  let W := c.orbit D
  let := (c.orbit_reduced D).normal
  let := (c.orbit_reduced D).elementary
  let := c.single_component_normal D hsingle
  let q := actionMk W
  let A := I.map q
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple A := (c.single_ff_action D hsingle n hn hF e).1
  have hc : pCore 2 A = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : A.Normal).isSubnormal,
      (c.orbit_reduced D).quotient_pCore_eq_bot,MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff _).mpr A.subtype_injective
  let i : I ≃* c.overcomponent := subgroupOfEquivOfLe le_sup_left
  let f : c.overcomponent →* A := (q.subgroupMap I).comp i.symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective I).comp i.symm.surjective
  obtain ⟨hcontrol,hpair⟩ := comparison_geometry_of_quasisimple_core_cover f hf hc hqs hm
  exact c.borel_normalizes_of_single_geometry D hsingle e hcontrol hpair

/-- The rank-two action branch places the original Hall in the original orbit Borel. -/
theorem ComparisonConfiguration.hall_le_borel_of_single_action_rank_two
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    (hqs : IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hm : letI := (c.orbit_reduced D).normal
      ComparisonRankTwo ((c.overcomponent.subgroupOf (c.join D)).map (actionMk (c.orbit D)))) :
    B.map H.subtype ≤ sourceOrbitBorel T L :=
  c.hall_le_borel_of_normalizes D e
    (c.borel_normalizes_of_single_action_rank_two D hsingle hqs n hn hF e hm)
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 ChapterB.InternalThompsonAction

/-- The two small containing-action alternatives, with actual carrier isomorphisms. -/
def SmallComparisonAction (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
    ∃ d : ℕ, (d = 4 ∨ d = 5) ∧ Nonempty (X ≃* SL(d,ZMod 2))

/-- Inspect the actual small-action carriers without exposing the predicate's body. -/
theorem SmallComparisonAction.cases {X : Type*} [Group X] (h : SmallComparisonAction X) :
    Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      ∃ d : ℕ, (d = 4 ∨ d = 5) ∧ Nonempty (X ≃* SL(d,ZMod 2)) := h

/-- The genuine containing-model list separates rank-two geometry from the small carriers. -/
theorem comparison_rank_two_or_small {X : Type*} [Group X]
    (h : PointControl.Constrained.ContainingModel X) :
    ComparisonRankTwo X ∨ SmallComparisonAction X := by
  cases h with
  | linearThree F hn e =>
    exact Or.inl (ComparisonRankTwo.of_special_linear hn
      ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,⟨e⟩⟩)
  | symplecticFour F hn e =>
    exact Or.inl (ComparisonRankTwo.of_symplectic hn
      ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,
        ⟨e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv⟩⟩)
  | g2 F hn e =>
    exact Or.inl (ComparisonRankTwo.of_g2 hn
      ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,⟨e⟩⟩)
  | alternatingSeven e => exact Or.inr (Or.inl ⟨e⟩)
  | binaryLinear d hd e => exact Or.inr (Or.inr ⟨d,hd,⟨e⟩⟩)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- Only the nonquasisimple core quotient and the small actual action carriers remain after rank-two placement. -/
theorem ComparisonConfiguration.single_hall_placement_or_remaining
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    (hproper : c.component.map H.subtype < c.overcomponent)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    (B.map H.subtype ≤ sourceOrbitBorel T L) ∨
      (letI := (c.orbit_reduced D).normal;
        ¬ IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent) ∨
          SmallComparisonAction
            ((c.overcomponent.subgroupOf (c.join D)).map (actionMk (c.orbit D)))) := by
  by_cases hq : IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent)
  · rcases comparison_rank_two_or_small
      (c.single_action_model_of_quasisimple_proper D hsingle hq hproper n hn hF e) with hm | hm
    · exact Or.inl (c.hall_le_borel_of_single_action_rank_two D hsingle hq n hn hF e hm)
    · exact Or.inr (Or.inr hm)
  · exact Or.inr (Or.inl hq)
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
