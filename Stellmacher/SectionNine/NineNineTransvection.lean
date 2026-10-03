module
public import Stellmacher.SectionNine.NineNineCoreAction
public import Stellmacher.SectionNine.LemmaNineThree
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The initial transvection in Stellmacher (9.9)

Once the reversed (9.8) application places the terminal neighbor-center
module in the first-step two-core, an actual element of the initial center
outside the terminal core induces an order-two displacement on the terminal
quotient module. Its full commutator is exactly the first-step center.

Criticality selects the element. The proved terminal-module centralizer
bound makes its displacement nontrivial, so the order-two full commutator
identifies it exactly. The first-step center is not contained in the
terminal center; their elementary abelian join therefore has relative
index two. The intermediate core containment is kept explicit so this
lemma does not depend on the unfinished numbered (9.8) distance bound.

Source: Stellmacher (9.9), opening paragraph on printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_initial_transvection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ actor : GAt ctx.Γ ctx.criticalPath.a',
      (actor : G) ∈ ZAt ctx.Γ ctx.criticalPath.a ∧
      (actor : G) ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ =
        ZAt ctx.Γ ctx.criticalPath.firstStep ∧
      QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hfour := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).2
  have hfull := nine_nine_commutator_eq_of_initial_four ctx hcore hfour
  have hRnot := nine_nine_first_center_not_le_terminal_center_of_initial_four
    ctx hb hcore hfour
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨mover, hmover⟩
  have hcentral := nine_three_module_centralizer_core_at_vertex ctx cp.a' horbit
  have hlocal := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment
  obtain ⟨actor, hactor, hactorNot⟩ := Set.not_subset.mp cp.critical.2
  have hactorP : actor ∈ GAt Γ cp.a' := (hlocal.1.trans hlocal.2) hactor
  let actorP : GAt Γ cp.a' := ⟨actor, hactorP⟩
  have hbound : ⁅VAt Γ cp.a', Subgroup.zpowers actor⁆ ≤ ZAt Γ cp.firstStep := by
    rw [← hfull, Subgroup.commutator_comm (ZAt Γ cp.a) (VAt Γ cp.a')]
    exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)
  have hnonzero : ⁅VAt Γ cp.a', Subgroup.zpowers actor⁆ ≠ ⊥ := by
    intro hzero
    rw [Subgroup.commutator_comm] at hzero
    have hfix := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero
    exact hactorNot (hcentral (hfix (Subgroup.mem_zpowers actor)))
  have hRcard := (nine_next_center_and_commutator_of_initial_four
    ctx.toLocalContext hfour cp.firstStep ⟨1, Γ.act_one _⟩).1
  change Nat.card (ZAt Γ cp.firstStep) = 2 at hRcard
  obtain ⟨hZcard, hcomm⟩ := nine_next_center_and_commutator_of_initial_four
    ctx.toLocalContext hfour cp.a' horbit
  change Nat.card (ZAt Γ cp.a') = 2 at hZcard
  change ⁅VAt Γ cp.a', QAt Γ cp.a'⁆ = ZAt Γ cp.a' at hcomm
  have heq : ⁅VAt Γ cp.a', Subgroup.zpowers actor⁆ = ZAt Γ cp.firstStep := by
    have hh := (Subgroup.one_lt_card_iff_ne_bot _).mpr hnonzero
    exact Subgroup.eq_of_le_of_card_ge hbound (by omega)
  refine ⟨actorP, hactor, hactorNot, heq, ?_⟩
  change QuotientCardEq
    (⁅VAt Γ cp.a', Subgroup.zpowers actor⁆ ⊔ ZAt Γ cp.a') (ZAt Γ cp.a') 2
  rw [heq]
  have hRZ : ZAt Γ cp.firstStep ⊓ ZAt Γ cp.a' = ⊥ := by
    by_contra hne
    have hh := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have hequal : ZAt Γ cp.firstStep ⊓ ZAt Γ cp.a' = ZAt Γ cp.firstStep :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact hRnot (hequal ▸ inf_le_right)
  have hRle : ZAt Γ cp.firstStep ≤ VAt Γ cp.a' := by
    rw [← hfull]
    exact (nine_nine_terminal_action_of_core ctx.toLocalContext hcore).2.2.2.1.trans inf_le_right
  have hQP : QAt Γ cp.a' ≤ GAt Γ cp.a' := by
    rw [QAt, q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZle : ZAt Γ cp.a' ≤ VAt Γ cp.a' := by
    rw [← hcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQP.trans (stabilizer_le_normalizer_v Γ cp.a'))
  let _ : IsElementaryAbelian 2 (VAt Γ cp.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  have hab : VAt Γ cp.a' ≤ Subgroup.centralizer (VAt Γ cp.a' : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hnormalize : ZAt Γ cp.firstStep ≤
      Subgroup.normalizer (ZAt Γ cp.a' : Set G) :=
    hRle.trans (hab.trans ((Subgroup.centralizer_le hZle).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (ZAt Γ cp.a') (ZAt Γ cp.firstStep) hnormalize
  rw [inf_comm, hRZ, Subgroup.card_bot, hZcard, hRcard, one_mul, sup_comm] at hcard
  change Nat.card (ZAt Γ cp.firstStep ⊔ ZAt Γ cp.a' : Subgroup G) =
    2 * Nat.card (ZAt Γ cp.a')
  rw [← hcard, hZcard]

end Stellmacher.SectionNine