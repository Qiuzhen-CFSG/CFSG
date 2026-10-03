module
public import Stellmacher.SectionNine.NineSevenNoncontainedFirstCenter
public import Stellmacher.SectionNine.NineNextVModule
public import Theory.GroupAction.ElementaryEightActorLine
/-!
# Terminal-module containment in the first core

For an order-eight first module in the commuting critical-path setting,
if the critical commutator lies in the first center, then the terminal
module lies in the first core. The same conclusion follows from containment
of the terminal module in the initial stabilizer.

The critical commutator is nontrivial and its proposed first-center bound
makes it a line. The elementary-eight actor-line theorem propagates this
commutator from the initial center to the entire first module. The genuine
faithful quotient kernel then places every terminal actor in the first core.
For the stabilizer criterion, normalization bounds the critical commutator
by the initial center; its terminal-core containment and the known center
intersection put it in the first center.

These reductions support both source terminal normality cases of Stellmacher
(9.7), printed p.54 / PDF p.44. They require no neighborhood-join definition
and retain Hypothesis Two on the original ambient group.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem nine_seven_terminal_module_le_first_core_of_commutator_line
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hline : ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep) :
    VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let A := VAt Γ cp.a'
  let P := ZAt Γ cp.a
  let Z := ZAt Γ cp.firstStep
  have hdata := nine_next_center_and_commutator_of_initial_four ctx.toLocalContext hfour
    cp.firstStep ⟨1, Γ.act_one _⟩
  have hZcard : Nat.card Z = 2 := hdata.1
  have hR : ⁅A,P⁆ = Z := Subgroup.eq_of_le_of_card_ge hline (by
    rw [hZcard]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr
      (nine_seven_terminal_initial_commutator_ne_bot ctx))
  have hV : IsElementaryAbelian 2 V :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have hA : IsElementaryAbelian 2 A :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  let _ := hV
  let _ := hA
  have hAG : A ≤ GAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  have hcomm : ⁅V,A⁆ ≤ Z := by
    rw [Subgroup.elementaryEight_commutator_line_of_subgroup V A P hfirstCard
      (hAG.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
      (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
      (by rw [Subgroup.commutator_comm, hR]; exact hZcard), Subgroup.commutator_comm, hR]
  have hkernel := (nine_next_v_module_kernel_of_center_and_commutator ctx hb cp.firstStep
    ⟨1, Γ.act_one _⟩ hZcard hdata.2).2.2
  intro actor hactor
  exact (hkernel actor (hAG hactor)).mp
    ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)).trans hcomm)

public theorem nine_seven_terminal_module_le_first_core_of_initial_stabilizer
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hcontained : VAt ctx.Γ ctx.criticalPath.a' ≤ GAt ctx.Γ ctx.criticalPath.a) :
    VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  apply nine_seven_terminal_module_le_first_core_of_commutator_line ctx hb hfirstCard hfour
  have hRinitial : ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      (hcontained.trans (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a))
  have hRterminal : ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      QAt ctx.Γ ctx.criticalPath.a' :=
    ((nine_seven_terminal_initial_commutator_le_modules ctx).trans inf_le_right).trans
      (nine_seven_module_le_own_core ctx.toLocalContext hb ctx.criticalPath.a')
  exact (le_inf hRinitial hRterminal).trans
    (nine_seven_initial_center_terminal_core_le_first_center ctx hfour)

end Stellmacher.SectionNine
