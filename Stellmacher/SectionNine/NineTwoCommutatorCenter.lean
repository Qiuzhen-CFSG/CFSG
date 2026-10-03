module

public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6
public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Stellmacher.SectionNine.NineTwoLocalIndex
public import Stellmacher.SectionNine.NineTwoCenterSectionSixModule
public import Stellmacher.SectionNine.NineTwoCentralizerGeneration
public import Stellmacher.SectionFiveToSeven.SixFourQuadraticCriticalFixed
public import Stellmacher.SectionFiveToSeven.Result6_4

/-!
# The ambient commutator-center step in Stellmacher (9.2)

For the normalized ambient Section Nine context, the neighboring core
intersection acts on the initial center with fixed index two. The generating
neighbor and the corrected core noncontainment force its commutator into
the next vertex center. Hypothesis Two stays on the original ambient group.

The index-two intersection first puts X=[Z_a,Q] in both local centers,
while (7.4) makes the action nontrivial; the second core centralizes its
center, so the action is quadratic. Map to the original group and identify
Z_a with the actual Section Six module. The canonical quotient-action bridge
makes the barred critical subgroup nontrivial and gives fixedness of X
under its entire preimage, using the elementary-abelian conclusion (1.7)(b).

By (7.5), the next center maps to the Sylow omega-center and is centralized
by P₂. For each w in X, the other core centralizes w. Unique maximality over
the edge Sylow turns the given generating equality into generation by that
core and the Sylow itself. Thus the centralizer join generates P₂. If w
were outside the next center, the exact canonical barred statement (6.4)
would forbid this generation. The original three local reductions are
retained as public inputs to the surrounding development.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.2), printed p.48 /
PDF p.38 of `refs/files/stellmacher-n-group.pdf`, using (1.7), (6.4), and
(7.3)--(7.5). The scan-correct core noncontainment and the full barred
preimage from (6.4) are retained. The unique-maximal argument uses the
original generation hypothesis directly.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

private theorem commutator_le_intersection_of_index_two
    {G : Type u} [Group G] [Finite G] (left right actor : Subgroup G)
    (hnorm : actor ≤ Subgroup.normalizer (left : Set G))
    (hcentral : actor ≤ Subgroup.centralizer (right : Set G))
    (hindex : QuotientCardEq left (left ⊓ right) 2) :
    ⁅left, actor⁆ ≤ left ⊓ right := by
  let intersection := (left ⊓ right).subgroupOf left
  have hcard : Nat.card intersection = Nat.card ↥(left ⊓ right) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hi : intersection.index = 2 := by
    have heq := intersection.index_mul_card
    rw [hcard, hindex] at heq
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos heq
  apply Subgroup.commutator_le.mpr
  intro vector hvector mover hmover
  have hconj : mover * vector⁻¹ * mover⁻¹ ∈ left :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hmover) _).mp (left.inv_mem hvector)
  have hsame : (⟨vector, hvector⟩ : left) ∈ intersection ↔
      (⟨mover * vector⁻¹ * mover⁻¹, hconj⟩ : left) ∈ intersection := by
    change vector ∈ left ∧ vector ∈ right ↔
      mover * vector⁻¹ * mover⁻¹ ∈ left ∧ mover * vector⁻¹ * mover⁻¹ ∈ right
    simp only [hvector, hconj, true_and]
    exact right.inv_mem_iff.symm.trans
      (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.centralizer_le_normalizer _) (hcentral hmover)) _)
  have hm := (intersection.mul_mem_iff_of_index_two hi).mpr hsame
  change vector * (mover * vector⁻¹ * mover⁻¹) ∈ left ⊓ right at hm
  simpa only [commutatorElement_def, mul_assoc] using hm

public theorem nine_two_commutator_intersection
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (m : Γ.Vertex) (hm : m ∈ Neighborhood Γ cp.firstStep)
    (hindex : QuotientCardEq (ZAt Γ cp.a) (ZAt Γ cp.a ⊓ ZAt Γ m) 2) :
    ⁅ZAt Γ cp.a, QAt Γ cp.firstStep ⊓ QAt Γ m⁆ ≤ ZAt Γ cp.a ⊓ ZAt Γ m := by
  have hnorm : q Γ cp.firstStep ⊓ q Γ m ≤
      Subgroup.normalizer (z Γ cp.a : Set G) :=
    (inf_le_left.trans (local_cores_le_edge_sylow h Γ cp).2).trans
      ((edge_sylow_data h Γ cp).1.1.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hmneighbor : cp.firstStep ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hm))
  have hcentral : z Γ m ≤ Subgroup.centralizer (q Γ m : Set G) :=
    ((lemma_seven_three h Γ).center_core m cp.firstStep hmneighbor).trans
      ((omegaOneCenter_le_centerAmbient (q Γ m)).trans
        (centerAmbient_le_centralizer (q Γ m)))
  exact commutator_le_intersection_of_index_two _ _ _ hnorm
    (inf_le_right.trans (Subgroup.le_centralizer_iff.mp hcentral)) hindex

public theorem nine_two_commutator_nontrivial
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (m : Γ.Vertex) (hnot : ¬ QAt Γ cp.firstStep ⊓ QAt Γ m ≤ QAt Γ cp.a) :
    ⁅ZAt Γ cp.a, QAt Γ cp.firstStep ⊓ QAt Γ m⁆ ≠ ⊥ := by
  intro htrivial
  apply hnot
  have hcentral := Subgroup.le_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp htrivial)
  change q Γ cp.firstStep ⊓ q Γ m ≤ q Γ cp.a
  rw [← (lemma_seven_four h Γ cp).edge_centralizer]
  exact le_inf (inf_le_left.trans (local_cores_le_edge_sylow h Γ cp).2) hcentral

public theorem nine_two_commutator_quadratic
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (m : Γ.Vertex) (hm : m ∈ Neighborhood Γ cp.firstStep)
    (hindex : QuotientCardEq (ZAt Γ cp.a) (ZAt Γ cp.a ⊓ ZAt Γ m) 2) :
    ⁅⁅ZAt Γ cp.a, QAt Γ cp.firstStep ⊓ QAt Γ m⁆,
      QAt Γ cp.firstStep ⊓ QAt Γ m⁆ = ⊥ := by
  have hmneighbor : cp.firstStep ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hm))
  have hcentral : z Γ m ≤ Subgroup.centralizer (q Γ m : Set G) :=
    ((lemma_seven_three h Γ).center_core m cp.firstStep hmneighbor).trans
      ((omegaOneCenter_le_centerAmbient (q Γ m)).trans
        (centerAmbient_le_centralizer (q Γ m)))
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (((nine_two_commutator_intersection h Γ cp m hm hindex).trans inf_le_right).trans
      (hcentral.trans (Subgroup.centralizer_le inf_le_right)))


private theorem map_inf_centralizer
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (A K : Subgroup G) :
    (A ⊓ Subgroup.centralizer (K : Set G)).map f =
      A.map f ⊓ Subgroup.centralizer (K.map f : Set H) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f ha.1, ?_⟩
    change f a ∈ Subgroup.centralizer (K.map f : Set H)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp ha.2 k hk)
  · rintro _ ⟨⟨a, ha, rfl⟩, hcent⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    change a ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    apply hf
    simpa only [map_mul] using
      Subgroup.mem_centralizer_iff.mp hcent (f k) (Subgroup.mem_map_of_mem f hk)


public theorem nine_two_commutator_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (m : ctx.Γ.Vertex)
    (hm : m ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (hindex : QuotientCardEq (ZAt ctx.Γ ctx.criticalPath.a)
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ ZAt ctx.Γ m) 2)
    (hgenerate : QAt ctx.Γ m ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) = GAt ctx.Γ ctx.criticalPath.firstStep)
    (hnot : ¬ QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ m ≤
      QAt ctx.Γ ctx.criticalPath.a) :
    ⁅ZAt ctx.Γ ctx.criticalPath.a,QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ m⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Q := QAt Γ cp.firstStep ⊓ QAt Γ m
  let V := ZAt Γ cp.a
  have hsetup := nine_two_ambient_setup ctx
  have hfirstMap : (GAt Γ cp.a).map embedding = P1 := hsetup.2.1
  have hnextMap : (GAt Γ cp.firstStep).map embedding = P2 := hsetup.2.2.1
  have hVmap : V.map embedding = sectionSixV S P1 :=
    nine_two_center_eq_sectionSixV ctx hfirstMap
  have hnext := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center
  have homega : (ZAt Γ cp.firstStep).map embedding = omegaOneCenter S := by
    rw [show ZAt Γ cp.firstStep = omegaOneCenter T from hnext.1,← ctx.map_S]
    exact (omegaOneCenterAmbient_map_injective embedding ctx.embedding_injective T).symm
  obtain ⟨hQT,_,_,hfixedIndex⟩ :=
    nine_two_fixed_index ctx.sectionSeven Γ cp m hm hindex hnot
  have hQS : Q.map embedding ≤ S := by
    rw [← ctx.map_S]
    exact Subgroup.map_mono hQT
  have hindexAmbient : Nat.card (sectionSixV S P1) = 2 *
      Nat.card (sectionSixV S P1 ⊓ Subgroup.centralizer (Q.map embedding : Set H) : Subgroup H) := by
    rw [← hVmap,← map_inf_centralizer embedding ctx.embedding_injective V Q,
      Subgroup.card_map_of_injective ctx.embedding_injective,
      Subgroup.card_map_of_injective ctx.embedding_injective]
    exact hfixedIndex
  have hquadAmbient : ⁅⁅sectionSixV S P1,Q.map embedding⁆,Q.map embedding⁆ = ⊥ := by
    rw [← hVmap,← Subgroup.map_commutator,← Subgroup.map_commutator]
    rw [nine_two_commutator_quadratic ctx.sectionSeven Γ cp m hm hindex,Subgroup.map_bot]
  obtain ⟨hJ,hJfixed⟩ := sixFour_quadratic_index_two_barred_fixed ctx.hypothesisTwo
    (Q.map embedding) hQS hindexAmbient hquadAmbient
  have hcomm : ⁅P2,omegaOneCenter S⁆ = ⊥ := by
    rw [← hnextMap,← homega,← Subgroup.map_commutator]
    have hlocal : ⁅GAt Γ cp.firstStep,ZAt Γ cp.firstStep⁆ = ⊥ := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      apply Subgroup.le_centralizer_iff.mpr
      rw [show ZAt Γ cp.firstStep = omegaOneCenter (GAt Γ cp.firstStep) from hnext.2]
      exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
    rw [hlocal,Subgroup.map_bot]
  intro w hw
  have hinter := nine_two_commutator_intersection ctx.sectionSeven Γ cp m hm hindex hw
  have hwV : embedding w ∈ sectionSixV S P1 := hVmap ▸
    Subgroup.mem_map_of_mem embedding hinter.1
  have hwJ : embedding w ∈
      Subgroup.centralizer (sectionSixBarredCriticalPreimage ctx.hypothesisTwo : Set H) := by
    apply hJfixed
    rw [← hVmap,← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem embedding hw
  by_contra hwZ
  have hwOmega : embedding w ∉ omegaOneCenter S := by
    intro hwmap
    rw [← homega] at hwmap
    obtain ⟨w0,hw0,heq⟩ := hwmap
    exact hwZ (ctx.embedding_injective heq ▸ hw0)
  have hgenG := nine_two_centralizer_generation ctx.toLocalContext m hm hgenerate w hinter.2
  have hgenH : sectionSixCentralizerJoin P2 S (embedding w) = P2 := by
    have hmapped := congrArg (Subgroup.map embedding) hgenG
    change ((GAt Γ cp.firstStep ⊓ Subgroup.centralizer (Subgroup.zpowers w : Set G)) ⊔ T).map
      embedding = (GAt Γ cp.firstStep).map embedding at hmapped
    rw [Subgroup.map_sup,map_inf_centralizer embedding ctx.embedding_injective,
      embedding.map_zpowers w,hnextMap,ctx.map_S] at hmapped
    exact hmapped
  exact lemma_six_four S0 S P1 P2 ctx.hypothesisTwo (sectionSixV S P1) rfl
    hcomm hJ (embedding w) hwV hwJ hwOmega hgenH.symm


end Stellmacher.SectionNine
