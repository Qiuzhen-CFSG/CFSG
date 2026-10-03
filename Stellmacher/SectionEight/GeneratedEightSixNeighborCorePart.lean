module
public import Stellmacher.SectionEight.GeneratedEightSixCoreImageAlgebra
public import Stellmacher.SectionEight.GeneratedEightSixCoreImageVWitness
public import Theory.GroupTheory.RelativeQuotientDisplacementCardinality

/-!
# The neighboring core part in Stellmacher (8.6)(1)

For the length-two critical configuration with initial quotient SL₂(2), the
first-step core intersected with the initial core is the join of its neighbor
module's core part and the actual opposite-core intersection D. The required
normality of D in the initial stabilizer and its core containment are explicit;
they are supplied by the existing upstream action theorem.

A cubic neighbor-module actor moves the opposite core to a conjugate whose
intersection lies in D. Commutator displacement is therefore injective modulo D
from the opposite core part into the first neighbor-module part joined with D.
Local transitivity gives equal orders for the two core parts. The quotient
cardinality inequality and the reverse containment then force equality.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed p.41,
equation (1). This supplies the core-part input to the subsequent orbit-cover
argument; no three-factor core-generation equality is assumed.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement
universe u

public theorem eight_six_neighbor_core_part_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hnormal : NormalIn D (GAt ctx.Γ ctx.criticalPath.a))
    (hDcore : D ≤ QAt ctx.Γ ctx.criticalPath.a) :
    QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a =
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D := by
  classical
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let X := QAt graph previous ⊓ QAt graph path.a
  let Y := QAt graph path.firstStep ⊓ QAt graph path.a
  let B := VAt graph path.firstStep ⊓ QAt graph path.a
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hlong : 1 < path.length := by dsimp [path]; omega
  have hqprev : QAt graph previous ≤ GAt graph path.a :=
    (eight_six_generation_neighbor_core_le ctx.sectionSeven graph path previous hprev.1).2
  have hqfirst : QAt graph path.firstStep ≤ GAt graph path.a :=
    (eight_six_generation_neighbor_core_le ctx.sectionSeven graph path path.firstStep hfirst).2
  have hqa : QAt graph path.a ≤ GAt graph path.a := by
    rw [QAt, q, graph.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  have hvfirst : VAt graph path.firstStep ≤ GAt graph path.a := by
    exact (SevenSix.neighbor_join_le_core_of_length_gt_one graph path hlong _).trans
      ((eight_six_generation_neighbor_core_le ctx.sectionSeven graph path path.firstStep hfirst).2)
  have hnormalizer : GAt graph path.a ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2
  have hcard : Nat.card X = Nat.card Y := by
    obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven graph).local_transitivity
      path.a hprev.1 hfirst
    let conjugation := (MulAut.conj (actor : G)⁻¹).toMonoidHom
    have hDmap : D.map conjugation = D :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer (D : Set G)).inv_mem (hnormalizer actor.property))
    have hQmap : (QAt graph path.a).map conjugation = QAt graph path.a :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer (QAt graph path.a : Set G)).inv_mem
          (SevenSix.stabilizer_le_normalizer_q graph path.a actor.property))
    have hVmap : (VAt graph previous).map conjugation = VAt graph path.firstStep := by
      rw [← hactor]
      exact (v_act graph actor previous).symm
    have hQprevMap : (QAt graph previous).map conjugation = QAt graph path.firstStep := by
      rw [← SevenSix.q_act, hactor]
    have hmap : X.map conjugation = Y := by
      dsimp [X, Y]
      rw [Subgroup.map_inf _ _ _ (MulAut.conj (actor : G)⁻¹).injective, hQprevMap, hQmap]
    rw [← hmap, Subgroup.card_map_of_injective
      (MulAut.conj (actor : G)⁻¹).injective]
  have hsubset : B ⊔ D ≤ Y := by
    apply sup_le
    · exact le_inf (inf_le_left.trans
        (SevenSix.neighbor_join_le_core_of_length_gt_one graph path hlong _)) inf_le_right
    · exact le_inf (hD.le.trans inf_le_right) hDcore
  have hD_X : D ≤ X := by
    exact le_inf (hD.le.trans inf_le_left) hDcore
  have hD_Y : D ≤ Y := by
    exact le_inf (hD.le.trans inf_le_right) hDcore
  obtain ⟨actor, hactor, hinter⟩ := eight_six_core_image_v_actor_local
    ctx hquot hlength previous hprev D hD hnormal
  have hcomm : ⁅QAt graph path.a, VAt graph path.firstStep⁆ ≤ B :=
    (eight_six_generation_neighbor_action ctx.sectionSeven graph path hlong
      path.firstStep hfirst).2
  let Z : Subgroup G := B ⊔ D
  let : (D.subgroupOf (GAt graph path.a)).Normal := hnormal.2
  have hquot_le' : Nat.card (X ⧸ D.subgroupOf X) ≤
      Nat.card ((Z ⊔ D : Subgroup G) ⧸ D.subgroupOf (Z ⊔ D)) := by
    apply Subgroup.quotient_card_le_of_conjugate_intersection_subgroupOf
      (GAt graph path.a) D X Z Y (QAt graph previous) (QAt graph path.a)
      (VAt graph path.firstStep) (actor := actor)
    · exact hDcore.trans hqa
    · exact inf_le_right.trans hqa
    · exact (sup_le (show B ≤ QAt graph path.a from inf_le_right) hDcore).trans hqa
    · exact inf_le_left.trans hqfirst
    · exact hqprev
    · exact hqa
    · exact hvfirst
    · exact hD_X
    · exact le_sup_right
    · exact inf_le_left
    · exact inf_le_right
    · exact hsubset
    · exact hD_Y
    · exact hcomm.trans le_sup_left
    · exact hactor
    · exact hinter
  have hquot_le : Nat.card (X ⧸ D.subgroupOf X) ≤
      Nat.card (Z ⧸ D.subgroupOf Z) := by
    have hZD : Z ⊔ D = Z := sup_eq_left.mpr le_sup_right
    rwa [hZD] at hquot_le'
  have hraw : Nat.card Z ≤ Nat.card Y := by
    exact Nat.card_mono (Set.toFinite _) hsubset
  have hDcardX : Nat.card (D.subgroupOf X) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_X).toEquiv
  have hDcardZ : Nat.card (D.subgroupOf Z) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hDcardY : Nat.card (D.subgroupOf Y) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_Y).toEquiv
  have hprodX := (D.subgroupOf X).card_mul_index
  have hprodZ := (D.subgroupOf Z).card_mul_index
  have hprodY := (D.subgroupOf Y).card_mul_index
  rw [Subgroup.index_eq_card] at hprodX hprodZ hprodY
  rw [hDcardX] at hprodX
  rw [hDcardZ] at hprodZ
  rw [hDcardY] at hprodY
  have hqX_eq : Nat.card (X ⧸ D.subgroupOf X) = Nat.card (Y ⧸ D.subgroupOf Y) := by
    apply Nat.le_antisymm <;>
      apply Nat.le_of_mul_le_mul_left (c := Nat.card D) _ (Nat.card_pos (α := D))
    · rw [hprodX, hprodY, hcard]
    · rw [hprodY, hprodX, hcard]
  have hqZ_le : Nat.card (Z ⧸ D.subgroupOf Z) ≤ Nat.card (Y ⧸ D.subgroupOf Y) := by
    apply Nat.le_of_mul_le_mul_left (c := Nat.card D) _ (Nat.card_pos (α := D))
    rw [hprodZ, hprodY]
    exact hraw
  have hqeq : Nat.card (Z ⧸ D.subgroupOf Z) = Nat.card (Y ⧸ D.subgroupOf Y) := by
    apply Nat.le_antisymm hqZ_le
    rw [← hqX_eq]
    exact hquot_le
  have hZcard : Nat.card Z = Nat.card Y := by
    rw [← hprodZ, ← hprodY, hqeq]
  exact (Subgroup.eq_of_le_of_card_ge hsubset hZcard.ge).symm
end Stellmacher.SectionEight
