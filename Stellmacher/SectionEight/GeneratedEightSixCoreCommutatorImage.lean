module

public import Stellmacher.SectionEight.GeneratedEightSixCoreImageAlgebra
public import Stellmacher.SectionEight.GeneratedEightSixCoreImageActor

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_core_commutator_image_of_actor
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData ctx.Γ ctx.criticalPath D L Q)
    (hgen : Q = (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D)
    (actor : G) (hactor : actor ∈ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hintersection : QAt ctx.Γ previous ⊓
      (QAt ctx.Γ previous).map (MulAut.conj actor).toMonoidHom ≤ D) :
    ⁅Q, QAt ctx.Γ ctx.criticalPath.firstStep⁆ ⊔ D =
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let initial := GAt graph path.a
  let core := QAt graph path.a
  let oldPart := VAt graph previous ⊓ core
  let newPart := VAt graph path.firstStep ⊓ core
  let oldFactor := oldPart ⊔ D
  let newFactor := newPart ⊔ D
  have hlong : 1 < path.length := by dsimp [path]; omega
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hfirstCores := eight_six_generation_neighbor_core_le ctx.sectionSeven
    graph path path.firstStep hfirst
  have hpreviousCores := eight_six_generation_neighbor_core_le ctx.sectionSeven
    graph path previous hprevious
  have hcontain := eight_six_action_core_containments ctx.sectionSeven graph path
    previous hprevious D L Q hD hL hQ action
  have hcoreInitial : core ≤ initial := by
    change QAt graph path.a ≤ GAt graph path.a
    rw [QAt, q, graph.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  have hDnormal : initial ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer action.intersection_normal.1).mp
      action.intersection_normal.2
  have hQnormal : initial ≤ Subgroup.normalizer (Q : Set G) := by
    rw [eight_six_generation_core_eq_inter ctx.sectionSeven graph path previous
      hprevious L Q hL hQ]
    apply le_trans (le_inf ?_ (SevenSix.stabilizer_le_normalizer_q graph path.a))
      Subgroup.inf_normalizer_le_normalizer_inf
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hVcore (vertex : graph.Vertex) : VAt graph vertex ≤ QAt graph vertex :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path hlong vertex
  have hDfirst : D ≤ QAt graph path.firstStep := hD.le.trans inf_le_right
  have hDprevious : D ≤ QAt graph previous := hD.le.trans inf_le_left
  have holdQ : oldFactor ≤ Q := sup_le
    (hgen ▸ le_sup_left.trans le_sup_left) hcontain.1
  have hnewQ : newFactor ≤ Q := sup_le
    (hgen ▸ le_sup_right.trans le_sup_left) hcontain.1
  have holdP : oldFactor ≤ QAt graph previous :=
    sup_le (inf_le_left.trans (hVcore previous)) hDprevious
  have hnewR : newFactor ≤ QAt graph path.firstStep :=
    sup_le (inf_le_left.trans (hVcore path.firstStep)) hDfirst
  have holdInter : oldFactor ⊓ QAt graph path.firstStep = D := by
    apply eight_six_sup_inter_eq_of_normalizes oldPart D _
      ((inf_le_right.trans hcoreInitial).trans hDnormal) hDfirst
    intro element helement
    rw [hD]
    exact ⟨hVcore previous helement.1.1, helement.2⟩
  have hnewNormal : core ≤ Subgroup.normalizer (newFactor : Set G) :=
    (le_inf (eight_six_generation_neighbor_action ctx.sectionSeven graph path hlong
      path.firstStep hfirst).1 (hcoreInitial.trans hDnormal)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hfactorGen : Q = oldFactor ⊔ newFactor := by
    rw [hgen]
    change oldPart ⊔ newPart ⊔ D = (oldPart ⊔ D) ⊔ (newPart ⊔ D)
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left)
        (le_sup_left.trans le_sup_right)) (le_sup_right.trans le_sup_left)
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hQinter : Q ⊓ QAt graph path.firstStep = newFactor := by
    rw [hfactorGen]
    apply eight_six_sup_inter_eq_of_normalizes oldFactor newFactor _
      ((holdQ.trans hcontain.2.1).trans hnewNormal) hnewR
    rw [holdInter]
    exact le_sup_right
  have hbound : ⁅Q, QAt graph path.firstStep⁆ ≤ newFactor := by
    rw [← hQinter]
    exact le_inf
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hfirstCores.2.trans hQnormal))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((hcontain.2.1.trans hfirstCores.1).trans
          (SevenSix.stabilizer_le_normalizer_q graph path.firstStep)))
  have hcard : Nat.card oldFactor = Nat.card newFactor := by
    obtain ⟨conjugator, hconjugator⟩ := (lemma_seven_one ctx.sectionSeven graph).local_transitivity
      path.a hprevious hfirst
    let conjugation := (MulAut.conj (conjugator : G)⁻¹).toMonoidHom
    have hDmap : D.map conjugation = D :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer (D : Set G)).inv_mem (hDnormal conjugator.property))
    have hcoreMap : core.map conjugation = core :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer (core : Set G)).inv_mem
          (SevenSix.stabilizer_le_normalizer_q graph path.a conjugator.property))
    have hVmap : (VAt graph previous).map conjugation = VAt graph path.firstStep := by
      rw [← hconjugator]
      exact (v_act graph conjugator previous).symm
    have hmap : oldFactor.map conjugation = newFactor := by
      dsimp only [oldFactor, oldPart, newFactor, newPart]
      rw [Subgroup.map_sup, Subgroup.map_inf _ _ _
        (MulAut.conj (conjugator : G)⁻¹).injective, hDmap, hcoreMap, hVmap]
    rw [← hmap, Subgroup.card_map_of_injective
      (MulAut.conj (conjugator : G)⁻¹).injective]
  exact eight_six_commutator_sup_eq_in_ambient initial D oldFactor newFactor
    (QAt graph previous) Q (QAt graph path.firstStep) action.intersection_normal
    hpreviousCores.2 (hcontain.2.1.trans hcoreInitial) hfirstCores.2
    ((hnewQ.trans hcontain.2.1).trans hcoreInitial) le_sup_right le_sup_right
    holdP holdQ hbound hcard actor hactor hintersection

public theorem generated_eight_six_core_commutator_image
    {H : Type u} [Group H] [Finite H] {S0 : Sylow 2 H}
    {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (_hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (_hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData ctx.Γ ctx.criticalPath D L Q)
    (hgen : Q = (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D) :
    ⁅Q, QAt ctx.Γ ctx.criticalPath.firstStep⁆ ⊔ D =
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D := by
  obtain ⟨actor, hactor, hintersection⟩ := eight_six_core_image_actor_local
    ctx.toLocalContext hquot hlength previous hprev D hD action.intersection_normal
  exact eight_six_core_commutator_image_of_actor ctx.toLocalContext hlength previous
    hprev.1 D L Q hD hL hQ action hgen actor hactor hintersection

end Stellmacher.SectionEight
