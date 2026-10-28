module

public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Stellmacher.SectionEight.GeneratedEightSixSylowIntersection
public import Stellmacher.SectionEight.CubicThreeSylowTransitivity

/-!
# Three-Sylow fixed-core bound in the small-index branch of (8.6)

The actual three-Sylow acts transitively on the initial neighborhood, so an
element conjugates the predecessor intersection generator to the first-step
generator. If a nontrivial point of the order-four core quotient were fixed,
the three-group automorphism image would have order at most two and hence be
trivial. The two conjugate generators would then have the same quotient image,
contradicting their generation of a quotient of order four from an image of
order two. This proves the fixed-core containment needed by the separate
barred-image intersection argument, without assuming nontrivial quotient action.

Source: Stellmacher, printed p.42 / PDF p.32, the small-index paragraph of
(8.6), in `refs/files/stellmacher-n-group.pdf`.
-/

open Stellmacher Later

namespace Stellmacher.SectionEight

public theorem three_group_action_four_fixed_imp_trivial
    {Actor Space : Type*} [Group Actor] [Group Space] [Finite Space]
    (hthree : IsPGroup 3 Actor) (hfour : Nat.card Space = 4)
    (action : Actor →* MulAut Space) (fixed : Space) (hne : fixed ≠ 1)
    (hfixed : ∀ actor, action actor fixed = fixed) : ∀ actor, action actor = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hbound : Nat.card action.range ≤ 2 :=
    card_mulAut_subgroup_le_two_of_fixed_point hfour fixed hne action.range (by
      rintro automorphism ⟨actor, rfl⟩
      exact hfixed actor)
  have hcard : Nat.card action.range = 1 := by
    rcases (hthree.of_surjective action.rangeRestrict
      action.rangeRestrict_surjective).card_eq_or_dvd with hone | hdiv
    · exact hone
    · have hpos : 0 < Nat.card action.range := Nat.card_pos
      have := Nat.le_of_dvd hpos hdiv
      omega
  have hbot : action.range = ⊥ := (Subgroup.eq_bot_iff_card _).mpr hcard
  intro actor
  have hmem : action actor ∈ action.range := ⟨actor, rfl⟩
  simpa only [hbot, Subgroup.mem_bot] using hmem

public theorem fixed_core_le_of_conjugate_generators
    {G : Type*} [Group G] [Finite G] (A B D Q T : Subgroup G)
    (hgen : Q = A ⊔ B ⊔ D)
    (hQD : Q ≤ Subgroup.normalizer D)
    (hTQ : T ≤ Subgroup.normalizer Q)
    (hTD : T ≤ Subgroup.normalizer D)
    (hthree : IsPGroup 3 T)
    (hindex : QuotientCardEq A (A ⊓ D) 2)
    (hquotient : QuotientCardEq Q D 4)
    (hconjugate : ∃ actor : T,
      A.map (MulAut.conj (actor : G)).toMonoidHom = B) :
    Q ⊓ Subgroup.centralizer (T : Set G) ≤ D := by
  have hAQ : A ≤ Q := hgen ▸ le_sup_of_le_left le_sup_left
  have hDQ : D ≤ Q := hgen ▸ le_sup_right
  let : (D.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQD
  let projection := QuotientGroup.mk' (D.subgroupOf Q)
  have hfour : Nat.card (Q ⧸ D.subgroupOf Q) = 4 := by
    have hproduct := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf Q)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv] at hproduct
    change Nat.card Q = 4 * Nat.card D at hquotient
    have hpos : 0 < Nat.card D := Nat.card_pos
    nlinarith
  obtain ⟨action, haction⟩ := Subgroup.exists_quotient_conjugation_action T Q D
    hTQ hTD (inferInstance : (D.subgroupOf Q).Normal)
  intro fixed hfixed
  by_contra houtside
  have hne : projection ⟨fixed, hfixed.1⟩ ≠ 1 := by
    intro heq
    exact houtside ((QuotientGroup.eq_one_iff (N := D.subgroupOf Q)
      (⟨fixed, hfixed.1⟩ : Q)).mp heq)
  have htrivial := three_group_action_four_fixed_imp_trivial hthree hfour action
    (projection ⟨fixed, hfixed.1⟩) hne (by
      intro actor
      rw [haction]
      apply congrArg projection
      apply Subtype.ext
      have hcomm := Subgroup.mem_centralizer_iff.mp hfixed.2 actor actor.property
      change (actor : G) * fixed * (actor : G)⁻¹ = fixed
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one])
  obtain ⟨actor, hactor⟩ := hconjugate
  have hBA : B ≤ A ⊔ D := by
    rw [← hactor]
    rintro element ⟨seed, hseed, rfl⟩
    have hconjQ : (actor : G) * seed * (actor : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hTQ actor.property) seed).mp (hAQ hseed)
    have heq : projection ⟨(actor : G) * seed * (actor : G)⁻¹, hconjQ⟩ =
        projection ⟨seed, hAQ hseed⟩ := by
      rw [← haction actor ⟨seed, hAQ hseed⟩, htrivial actor]
      rfl
    have hdiff : ((actor : G) * seed * (actor : G)⁻¹) / seed ∈ D :=
      QuotientGroup.eq_iff_div_mem (N := D.subgroupOf Q) |>.mp heq
    have hmem := (A ⊔ D).mul_mem
      ((le_sup_right : D ≤ A ⊔ D) hdiff)
      ((le_sup_left : A ≤ A ⊔ D) hseed)
    simpa only [div_mul_cancel, MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe] using hmem
  have hcollapse : Q = A ⊔ D := by
    rw [hgen]
    exact le_antisymm (sup_le (sup_le le_sup_left hBA) le_sup_right)
      (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
  have hproduct := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes D A
    (hAQ.trans hQD)
  rw [inf_comm D A, sup_comm D A, ← hcollapse] at hproduct
  change Nat.card A = 2 * Nat.card (A ⊓ D : Subgroup G) at hindex
  change Nat.card Q = 4 * Nat.card D at hquotient
  have hposD : 0 < Nat.card D := Nat.card_pos
  have hposAD : 0 < Nat.card (A ⊓ D : Subgroup G) := Nat.card_pos
  nlinarith

open SectionsFiveToSeven CosetGraphContext

public theorem eight_six_fixed_core_le_of_three_sylow_transitivity
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q T : Subgroup G)
    (hprevious : previous ∈ neighborhood graph path.a)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L) (hT : IsSylowIn 3 T (GAt graph path.a))
    (data : EightSixEquationOneData graph path previous D L Q)
    (hindex : QuotientCardEq (VAt graph previous ⊓ QAt graph path.a)
      ((VAt graph previous ⊓ QAt graph path.a) ⊓ D) 2)
    (hquotient : QuotientCardEq Q D 4)
    (htransitive : IsActionTransitiveOn graph T (neighborhood graph path.a)) :
    Q ⊓ Subgroup.centralizer (T : Set G) ≤ D := by
  obtain ⟨sylow, hsylow⟩ := hT
  have hTP : T ≤ GAt graph path.a := hsylow ▸ Subgroup.map_subtype_le _
  have hthree : IsPGroup 3 T := hsylow ▸ sylow.isPGroup'.map _
  have hLnormal : NormalIn L (GAt graph path.a) := by
    refine ⟨data.closure_le, Subgroup.normal_subgroupOf_of_le_normalizer ?_⟩
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hQP : Q ≤ GAt graph path.a := by
    rw [hQ]
    exact (SevenSix.twoCoreIn_le L).trans data.closure_le
  have hQnormal : (Q.subgroupOf (GAt graph path.a)).Normal := by
    rw [hQ]
    exact SevenSix.twoCoreIn_normal_of_normal _ _ data.closure_le hLnormal.2
  have hPQ : GAt graph path.a ≤ Subgroup.normalizer Q :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp hQnormal
  have hPD : GAt graph path.a ≤ Subgroup.normalizer D :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
      data.intersection_normal.2
  apply fixed_core_le_of_conjugate_generators
    (VAt graph previous ⊓ QAt graph path.a)
    (VAt graph path.firstStep ⊓ QAt graph path.a) D Q T
    data.core_generation (hQP.trans hPD) (hTP.trans hPQ) (hTP.trans hPD)
    hthree hindex hquotient
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  obtain ⟨actor, hactor⟩ := htransitive hprevious hfirst
  refine ⟨actor⁻¹, ?_⟩
  have hfix : graph.act (actor : G) path.a = path.a :=
    (Set.ext_iff.mp (graph.stabilizer_def path.a) (actor : G)).mp
      (hTP actor.property)
  change (v graph previous ⊓ q graph path.a).map
      (MulAut.conj (actor : G)⁻¹).toMonoidHom =
    v graph path.firstStep ⊓ q graph path.a
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (actor : G)⁻¹).injective,
    ← v_act graph (actor : G) previous,
    ← SevenSix.q_act graph (actor : G) path.a, hactor, hfix]

universe u

public theorem generated_eight_six_small_index_fixed_core_le_intersection
    {H : Type u} [Group H] [Finite H] {S0 : Sylow 2 H}
    {S P1 P2 : Subgroup H}
    (ctx : Later.GeneratedSectionEightContext H S0 S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hindex : QuotientCardEq
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hquotient : QuotientCardEq Q D 4) :
    Q ⊓ Subgroup.centralizer (T : Set (P1 ⊔ P2 : Subgroup H)) ≤ D := by
  exact eight_six_fixed_core_le_of_three_sylow_transitivity ctx.Γ ctx.criticalPath
    previous D L Q T hprev.1 hdefs.2.1 hdefs.2.2.1 hdefs.2.2.2 data hindex hquotient
    (cubic_three_sylow_transitive ctx.sectionSeven ctx.Γ ctx.criticalPath.a
      hquot T hdefs.2.2.2)

end Stellmacher.SectionEight
