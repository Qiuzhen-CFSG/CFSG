module

public import Stellmacher.SectionNine.NineNineInitialInputs
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs
public import Stellmacher.SectionNine.NineNextCenterCommutator
public import Stellmacher.SectionNine.NineNextVModule

/-!
# Core-containment action inputs for (9.9)(1)

The upstream terminal-core containment places the terminal module in the
distinguished edge Sylow subgroup. The two modules normalize each other,
their commutator lies in their intersection, and the terminal module fixes
the first-step center pointwise.

Given initial-center order four, the proved next-module calculation and
ambient nontrivial-action theorem identify the initial-center/terminal-module
commutator exactly. The actual quotient-kernel criterion also shows that
this commutator does not disappear modulo the terminal center. Initial
order four remains an explicit upstream premise from (9.3); no commutator
conclusion is assumed. Hypothesis Two stays on the original ambient group H.

Source: Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`. The support-existence theorem itself
is not claimed in this module.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_nine_terminal_action_of_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    VAt ctx.Γ ctx.criticalPath.a' ≤ T ∧
      VAt ctx.Γ ctx.criticalPath.a' ≤
        Subgroup.normalizer (ZAt ctx.Γ ctx.criticalPath.a : Set G) ∧
      ZAt ctx.Γ ctx.criticalPath.a ≤
        Subgroup.normalizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) ∧
      ⁅ZAt ctx.Γ ctx.criticalPath.a, VAt ctx.Γ ctx.criticalPath.a'⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.a ⊓ VAt ctx.Γ ctx.criticalPath.a' ∧
      VAt ctx.Γ ctx.criticalPath.a' ≤
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.firstStep : Set G) := by
  have hterminal := hcore.trans (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hnormalize := (hterminal.trans ctx.criticalPath.S_le_edge_stabilizers).trans
    (inf_le_left.trans (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a))
  have hinitial := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment
  have hreverse := (hinitial.1.trans hinitial.2).trans
    (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a')
  have hfirst : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.centralizer (QAt ctx.Γ ctx.criticalPath.firstStep : Set G) :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj))).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  refine ⟨hterminal, hnormalize, hreverse, le_inf ?_ ?_, ?_⟩
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp hnormalize
  · rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hreverse
  · exact hcore.trans (Subgroup.le_centralizer_iff.mp hfirst)

public theorem nine_nine_commutator_eq_of_initial_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ⁅ZAt ctx.Γ ctx.criticalPath.a, VAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  obtain ⟨hcard, hfirst⟩ := nine_next_center_and_commutator_of_initial_four
    ctx.toLocalContext hfour ctx.criticalPath.firstStep ⟨1, ctx.Γ.act_one _⟩
  change Nat.card (ZAt ctx.Γ ctx.criticalPath.firstStep) = 2 at hcard
  have hle := (Subgroup.commutator_mono
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1
    hcore).trans_eq hfirst
  have hnontrivial := nine_nine_initial_action_nontrivial ctx
  have hcommcard := (Subgroup.one_lt_card_iff_ne_bot _).mpr hnontrivial
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

public theorem nine_nine_first_center_not_le_terminal_center_of_initial_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ ZAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨actor, _, halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep ctx.criticalPath.a' :=
    ⟨actor, halignment⟩
  obtain ⟨hcard, hcomm⟩ := nine_next_center_and_commutator_of_initial_four
    ctx.toLocalContext hfour ctx.criticalPath.a' horbit
  have hkernel := (nine_next_v_module_kernel_of_center_and_commutator ctx hb
    ctx.criticalPath.a' horbit hcard hcomm).2.2
  have hfull := nine_nine_commutator_eq_of_initial_four ctx hcore hfour
  have hlocal := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment
  intro hcontain
  apply ctx.criticalPath.critical.2
  intro mover hmover
  apply (hkernel mover ((hlocal.1.trans hlocal.2) hmover)).mp
  have hbound : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers mover⁆ ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ :=
    Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hmover)
  rw [Subgroup.commutator_comm (VAt ctx.Γ ctx.criticalPath.a')
    (ZAt ctx.Γ ctx.criticalPath.a), hfull] at hbound
  exact hbound.trans hcontain

end Stellmacher.SectionNine
