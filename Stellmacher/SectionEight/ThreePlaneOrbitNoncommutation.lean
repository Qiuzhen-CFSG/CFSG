module

public import Stellmacher.SectionEight.GeneratedEightSixNextConjugateGeometry

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

private theorem plane_conjugate_one {G : Type u} [Group G] (plane : Subgroup G) :
    conjugateBy plane 1 = plane := by
  ext element
  simp [conjugateBy, Subgroup.mem_map]

private theorem plane_conjugate_mul {G : Type u} [Group G]
    (plane : Subgroup G) (left right : G) :
    conjugateBy plane (left * right) = conjugateBy (conjugateBy plane right) left := by
  simp only [conjugateBy, Subgroup.map_map]
  congr 1
  ext element
  change (left * right) * element * (left * right)⁻¹ =
    left * (right * element * right⁻¹) * left⁻¹
  group

@[instance_reducible] private def planeAction {G : Type u} [Group G] (actors : Subgroup G) :
    MulAction actors (Subgroup G) where
  smul actor plane := conjugateBy plane actor
  one_smul := plane_conjugate_one
  mul_smul left right plane := plane_conjugate_mul plane left right

private theorem plane_orbit_card {G : Type u} [Group G] [Finite G]
    (seed actors : Subgroup G)
    (hindex : ((Subgroup.normalizer (seed : Set G)).subgroupOf actors).index = 3) :
    let _ := planeAction actors
    Nat.card (MulAction.orbit actors seed) = 3 := by
  let _ := planeAction actors
  change Nat.card (MulAction.orbit actors seed) = 3
  have hstabilizer : MulAction.stabilizer actors seed =
      (Subgroup.normalizer (seed : Set G)).subgroupOf actors := by
    ext actor
    exact Subgroup.mem_normalizer_iff_map_conj_eq.symm
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer actors seed),
    ← Subgroup.index_eq_card, hstabilizer, hindex]

private theorem conjugate_commutator_bot {G : Type u} [Group G]
    (left right : Subgroup G) (actor : G) :
    ⁅conjugateBy left actor, conjugateBy right actor⁆ = ⊥ ↔ ⁅left, right⁆ = ⊥ := by
  simp only [conjugateBy, ← Subgroup.map_commutator]
  exact Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj actor).injective

private theorem three_relation_cycle {A X : Type*} [Group A] [MulAction A X]
    (relation : X → X → Prop) (first second third : X)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hcover : ∀ point, point = first ∨ point = second ∨ point = third)
    (htransitive : ∀ source target : X, ∃ actor : A, actor • source = target)
    (hsymmetric : ∀ left right, relation left right → relation right left)
    (hinvariant : ∀ (actor : A) left right,
      relation left right → relation (actor • left) (actor • right))
    (hrelated : relation first second) : relation second third := by
  obtain ⟨actor, hactor⟩ := htransitive third first
  have hleft : actor • first ≠ first := by
    exact fun hequal => hfirstThird ((MulAction.injective actor) (hequal.trans hactor.symm))
  have hright : actor • second ≠ first := by
    exact fun hequal => hsecondThird ((MulAction.injective actor) (hequal.trans hactor.symm))
  have hdistinct : actor • first ≠ actor • second :=
    fun hequal => hfirstSecond ((MulAction.injective actor) hequal)
  have htransported := hinvariant actor first second hrelated
  rcases hcover (actor • first) with hequal | hequal | hequal
  · exact (hleft hequal).elim
  · rcases hcover (actor • second) with hother | hother | hother
    · exact (hright hother).elim
    · exact (hdistinct (hequal.trans hother.symm)).elim
    · simpa only [hequal, hother] using htransported
  · rcases hcover (actor • second) with hother | hother | hother
    · exact (hright hother).elim
    · exact hsymmetric _ _ (by simpa only [hequal, hother] using htransported)
    · exact (hdistinct (hequal.trans hother.symm)).elim

private theorem commuting_sup_left {G : Type u} [Group G]
    (first second target : Subgroup G)
    (hfirst : ⁅first, target⁆ = ⊥) (hsecond : ⁅second, target⁆ = ⊥) :
    ⁅first ⊔ second, target⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at *
  exact sup_le hfirst hsecond

private theorem commuting_three_join {G : Type u} [Group G]
    (first second third : Subgroup G)
    (hfirst : ⁅first, first⁆ = ⊥) (hsecond : ⁅second, second⁆ = ⊥)
    (hthird : ⁅third, third⁆ = ⊥)
    (hfirstSecond : ⁅first, second⁆ = ⊥)
    (hsecondThird : ⁅second, third⁆ = ⊥)
    (hfirstThird : ⁅first, third⁆ = ⊥) :
    ⁅first ⊔ second ⊔ third, first ⊔ second ⊔ third⁆ = ⊥ := by
  have hcomm (left right : Subgroup G) : ⁅left, right⁆ = ⊥ → ⁅right, left⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact id
  apply commuting_sup_left
  · apply commuting_sup_left
    · apply hcomm
      exact commuting_sup_left _ _ _
        (commuting_sup_left _ _ _ hfirst (hcomm _ _ hfirstSecond))
        (hcomm _ _ hfirstThird)
    · apply hcomm
      exact commuting_sup_left _ _ _
        (commuting_sup_left _ _ _ hfirstSecond hsecond) (hcomm _ _ hsecondThird)
  · apply hcomm
    exact commuting_sup_left _ _ _
      (commuting_sup_left _ _ _ hfirstThird hsecondThird) hthird

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
public theorem three_plane_pairwise_noncommuting_geometry
    {G : Type u} [Group G] [Finite G]
    (seed actors common whole : Subgroup G)
    (hseedActors : seed ≤ actors)
    (helementary : IsElementaryAbelian 2 seed)
    (hseedCard : Nat.card seed = 4)
    (hcommonCard : Nat.card common = 2)
    (hcommonSeed : common ≤ seed)
    (hcentral : actors ≤ Subgroup.centralizer (common : Set G))
    (hgeneration : whole = conjugateClosure seed actors)
    (hderived : ⁅whole, whole⁆ = common)
    (horbit : ((Subgroup.normalizer (seed : Set G)).subgroupOf actors).index = 3)
    (hsmall : Nat.card whole ≤ 16) :
    ∃ secondPlane thirdPlane : Subgroup G,
      IsElementaryAbelian 2 secondPlane ∧ IsElementaryAbelian 2 thirdPlane ∧
      Nat.card secondPlane = 4 ∧ Nat.card thirdPlane = 4 ∧
      common ≤ secondPlane ∧ common ≤ thirdPlane ∧
      whole = seed ⊔ secondPlane ⊔ thirdPlane ∧
      ⁅seed, secondPlane⁆ ≠ ⊥ ∧ ⁅secondPlane, thirdPlane⁆ ≠ ⊥ ∧
      ⁅seed, thirdPlane⁆ ≠ ⊥ := by
  classical
  let _ := helementary
  let _ := planeAction actors
  obtain ⟨firstActor, secondActor, thirdActor, henumeration⟩ :=
    eight_six_three_conjugates_of_index_three seed actors
      ((Subgroup.normalizer (seed : Set G)).subgroupOf actors)
      (by rintro element ⟨actor, hactor, rfl⟩; exact hactor) horbit
  let first : MulAction.orbit actors seed :=
    ⟨conjugateBy seed firstActor, ⟨firstActor, rfl⟩⟩
  let second : MulAction.orbit actors seed :=
    ⟨conjugateBy seed secondActor, ⟨secondActor, rfl⟩⟩
  let third : MulAction.orbit actors seed :=
    ⟨conjugateBy seed thirdActor, ⟨thirdActor, rfl⟩⟩
  have hcover : ∀ point : MulAction.orbit actors seed,
      point = first ∨ point = second ∨ point = third := by
    rintro ⟨plane, actor, hactor⟩
    rcases henumeration actor with hequal | hequal | hequal
    · exact Or.inl (Subtype.ext (hactor.symm.trans hequal))
    · exact Or.inr (Or.inl (Subtype.ext (hactor.symm.trans hequal)))
    · exact Or.inr (Or.inr (Subtype.ext (hactor.symm.trans hequal)))
  let enumeration : Fin 3 → MulAction.orbit actors seed := ![first, second, third]
  have hsurjective : Function.Surjective enumeration := by
    intro point
    rcases hcover point with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hinjective : Function.Injective enumeration :=
    ((Nat.bijective_iff_surjective_and_card enumeration).mpr
      ⟨hsurjective, by simpa using (plane_orbit_card seed actors horbit).symm⟩).1
  have hfirstSecond : first ≠ second := by
    intro hequal
    have := hinjective (show enumeration 0 = enumeration 1 from hequal)
    exact (by decide : (0 : Fin 3) ≠ 1) this
  have hfirstThird : first ≠ third := by
    intro hequal
    have := hinjective (show enumeration 0 = enumeration 2 from hequal)
    exact (by decide : (0 : Fin 3) ≠ 2) this
  have hsecondThird : second ≠ third := by
    intro hequal
    have := hinjective (show enumeration 1 = enumeration 2 from hequal)
    exact (by decide : (1 : Fin 3) ≠ 2) this
  have htransitive : ∀ source target : MulAction.orbit actors seed,
      ∃ actor : actors, actor • source = target := by
    rintro ⟨source, sourceActor, hsource⟩ ⟨target, targetActor, htarget⟩
    refine ⟨targetActor * sourceActor⁻¹, Subtype.ext ?_⟩
    change (targetActor * sourceActor⁻¹) • source = target
    rw [← hsource, ← mul_smul]
    simpa using htarget
  let relation (left right : MulAction.orbit actors seed) : Prop :=
    ⁅left.val, right.val⁆ = ⊥
  have hsymmetric : ∀ left right, relation left right → relation right left := by
    intro left right
    dsimp only [relation]
    rw [Subgroup.commutator_comm]
    exact id
  have hinvariant : ∀ (actor : actors) left right,
      relation left right → relation (actor • left) (actor • right) := by
    intro actor left right hrelation
    exact (conjugate_commutator_bot left.val right.val actor).mpr hrelation
  have hcycleFirst : relation first second → relation second third :=
    three_relation_cycle relation first second third hfirstSecond hfirstThird
      hsecondThird hcover htransitive hsymmetric hinvariant
  have hcycleSecond : relation second third → relation third first :=
    three_relation_cycle relation second third first hsecondThird hfirstSecond.symm
      hfirstThird.symm (by
        intro point
        rcases hcover point with hequal | hequal | hequal
        · exact Or.inr (Or.inr hequal)
        · exact Or.inl hequal
        · exact Or.inr (Or.inl hequal))
      htransitive hsymmetric hinvariant
  have hcycleThird : relation third first → relation first second :=
    three_relation_cycle relation third first second hfirstThird.symm hsecondThird.symm
      hfirstSecond (by
        intro point
        rcases hcover point with hequal | hequal | hequal
        · exact Or.inr (Or.inl hequal)
        · exact Or.inr (Or.inr hequal)
        · exact Or.inl hequal)
      htransitive hsymmetric hinvariant
  have hconjugateLe (actor : actors) : conjugateBy seed actor ≤ whole := by
    rw [hgeneration]
    rintro element ⟨representative, hrepresentative, rfl⟩
    exact Subgroup.subset_closure ⟨actor, ⟨representative, hrepresentative⟩, rfl⟩
  have hjoin : whole = first.val ⊔ second.val ⊔ third.val := by
    apply le_antisymm
    · rw [hgeneration]
      apply (Subgroup.closure_le _).mpr
      rintro element ⟨actor, representative, rfl⟩
      have hmem : (actor : G) * (representative : G) * (actor : G)⁻¹ ∈
          conjugateBy seed actor :=
        Subgroup.mem_map.mpr ⟨representative, representative.property, rfl⟩
      rcases henumeration actor with hequal | hequal | hequal
      · rw [hequal] at hmem
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hmem)
      · rw [hequal] at hmem
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hmem)
      · rw [hequal] at hmem
        exact Subgroup.mem_sup_right hmem
    · exact sup_le (sup_le (hconjugateLe firstActor) (hconjugateLe secondActor))
        (hconjugateLe thirdActor)
  have hdata (actor : actors) :
      IsElementaryAbelian 2 (conjugateBy seed actor) ∧
      Nat.card (conjugateBy seed actor) = 4 ∧ common ≤ conjugateBy seed actor := by
    refine ⟨IsElementaryAbelian.map (MulAut.conj (actor : G)).toMonoidHom, ?_, ?_⟩
    · exact (Subgroup.card_map_of_injective (MulAut.conj (actor : G)).injective).trans
        hseedCard
    · exact eight_six_common_line_le_conjugate seed actors common hcommonSeed
        (hcentral.trans (Subgroup.centralizer_le_normalizer _)) actor
  have hself (actor : actors) : ⁅conjugateBy seed actor, conjugateBy seed actor⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr (hdata actor).1.toIsMulCommutative
  have hnotall : ¬ (relation first second ∧ relation second third ∧
      relation first third) := by
    rintro ⟨hfirst, hsecond, hthird⟩
    have hbot : ⁅whole, whole⁆ = ⊥ := by
      rw [hjoin]
      exact commuting_three_join _ _ _ (hself firstActor) (hself secondActor)
        (hself thirdActor) hfirst hsecond hthird
    have hcommonBot : common = ⊥ := hderived.symm.trans hbot
    rw [hcommonBot] at hcommonCard
    simp at hcommonCard
  have hnonFirst : ¬ relation first second := fun hfirst =>
    hnotall ⟨hfirst, hcycleFirst hfirst,
      hsymmetric _ _ (hcycleSecond (hcycleFirst hfirst))⟩
  have hnonSecond : ¬ relation second third := fun hsecond =>
    hnonFirst (hcycleThird (hcycleSecond hsecond))
  have hnonThird : ¬ relation first third := fun hthird =>
    hnonFirst (hcycleThird (hsymmetric _ _ hthird))
  have hseed : seed = first.val ∨ seed = second.val ∨ seed = third.val := by
    simpa only [Subgroup.coe_one, plane_conjugate_one] using henumeration 1
  rcases hseed with hseed | hseed | hseed
  · refine ⟨second.val, third.val, (hdata secondActor).1, (hdata thirdActor).1,
      (hdata secondActor).2.1, (hdata thirdActor).2.1,
      (hdata secondActor).2.2, (hdata thirdActor).2.2, ?_, ?_, hnonSecond, ?_⟩
    · simpa only [hseed] using hjoin
    · simpa only [hseed] using hnonFirst
    · simpa only [hseed] using hnonThird
  · refine ⟨first.val, third.val, (hdata firstActor).1, (hdata thirdActor).1,
      (hdata firstActor).2.1, (hdata thirdActor).2.1,
      (hdata firstActor).2.2, (hdata thirdActor).2.2, ?_, ?_, hnonThird, ?_⟩
    · simp only [hseed]
      rw [sup_comm second.val first.val]
      exact hjoin
    · simp only [hseed]
      rw [Subgroup.commutator_comm]
      exact hnonFirst
    · simpa only [hseed] using hnonSecond
  · refine ⟨first.val, second.val, (hdata firstActor).1, (hdata secondActor).1,
      (hdata firstActor).2.1, (hdata secondActor).2.1,
      (hdata firstActor).2.2, (hdata secondActor).2.2, ?_, ?_, hnonFirst, ?_⟩
    · simp only [hseed]
      exact hjoin.trans (by ac_rfl)
    · simp only [hseed]
      rw [Subgroup.commutator_comm]
      exact hnonThird
    · simp only [hseed]
      rw [Subgroup.commutator_comm]
      exact hnonSecond

end Stellmacher.SectionEight
