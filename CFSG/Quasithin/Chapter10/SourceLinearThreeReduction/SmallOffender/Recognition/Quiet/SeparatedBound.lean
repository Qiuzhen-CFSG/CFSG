module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.RankBound

/-!
# The separated quiet offender bound without a cubic-order hypothesis

Crossed centralization supplies TI for the moved group directly. Uniform
fixed spaces normalize each moved offender, whose component stabilizer
embeds in the component automorphism group. The resulting bound on the
moved group applies even to three-free Suzuki quotients.

The Suzuki application is in Quiet.Suzuki. Source: Aschbacher--Smith
10.1.1 and 10.2.9--12, printed pp.741,750--755.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE ChapterI.Section06To08 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Crossed factors supply the size bound independently of the component order. -/
theorem quiet_moved_card_le_of_crossed_automorphism_rank
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hcross : ∀ {t : G}, t ∈ (T : Subgroup G) → t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {r : ℕ} (hrank : primeRank 2 (MulAut (L ⧸ pCore 2 L)) ≤ r) :
    Nat.card (⁅D.fullModule,L⁆ : Subgroup G) ≤ 2 ^ (r + 3) := by
  by_contra! hlarge
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  have hz := quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ
  have hti := quiet_moved_ti_of_crossed D c hJ hNL ht htn (hcross ht htn)
  have hsize : 8 < (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ := by
    rw [←inf_relIndex_left,hz,relIndex_bot_left]
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ r + 3)).trans_lt hlarge
  let ctx : FixedSpaces.Context D :=
    ⟨c.many,c.minimal,c.nonnormal,c.notA5,c.pointCentralizers,
      fun _ ht htn => hcross ht htn,hsize⟩
  have hgeometry := FixedSpaces.fixedSpaceGeometry_of_normalizer D ctx hNL
  apply c.noncommuting
  apply source_a5_small_conjugates_commute_of_moved_factor D c.nonnormal ht
    (hcross ht htn) 2 ?_ g c.small
  intro x hx hs
  have hc : ⁅⁅D.fullModule,L⁆,(⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom⁆ = ⊥ := by
    by_contra hnc
    have hd : Disjoint ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom) :=
      disjoint_iff.mpr (FixedSpaces.moved_inf_conjugate_eq_bot D c.nonnormal t ht
        (hcross ht htn) c.pointCentralizers hNL hx)
    exact (not_lt_of_ge (moved_ti_card_le_of_automorphism_rank D c.nonnormal hti hz
      hrank hd hnc hs (hgeometry x hx hs).1)) hlarge
  have hp := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  refine ⟨?_,hp⟩
  obtain ⟨w,hw,hw1⟩ := (⁅D.fullModule,L⁆ : Subgroup G).bot_or_exists_ne_one.resolve_left
    (source_full_moved_ne_bot D)
  exact (hp.trans (centralizer_le (Set.singleton_subset_iff.mpr hw))).trans
    (c.pointCentralizers w hw hw1)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
