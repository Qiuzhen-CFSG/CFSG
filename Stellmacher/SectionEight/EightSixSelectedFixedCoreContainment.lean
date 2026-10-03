module
public import Stellmacher.SectionEight.EightSixFixedCoreEscapeActionBound
public import Stellmacher.SectionEight.EightSixResidualFixedDecomposition
public import Stellmacher.SectionEight.EightSixSelectedActorNontransvection

/-!
For the actual selected minimum-cost actor in the large-index branch, the
residual-fixed part V0 of the next core lies in the initial core, while its
residual commutator Y does not. If V0 escaped, the proved core-generation
calculation would bound the actor's displacement modulo its literal fixed
subgroup by two. The selected-actor nontransvection theorem gives a strictly
larger index, proving the first containment.

The literal quotient action and the proved residual fixed decomposition
then express Vnext as its residual commutator joined with its fixed subgroup.
If Y also lay in the initial core, so would Vnext. Its terminal critical
center would centralize the initial center, contrary to the critical pair.
This assembles assertion (14) of Stellmacher's Lemma 8.6, printed p.44,
without any raw small-action model or assumed classification alternative.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_selected_fixed_core_containment
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other) :
    (QAt ctx.Γ ctx.criticalPath.firstStep ⊓ Subgroup.centralizer (twoResidualIn E : Set G) ≤
      QAt ctx.Γ ctx.criticalPath.a) ∧
      ¬ ⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ ≤ QAt ctx.Γ ctx.criticalPath.a := by
  have hE := geom.group_le
  have hAE : VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a ≤ E :=
    geom.generated ▸ le_sup_left
  have hindex := eight_six_selected_actor_not_transvection ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin
  obtain ⟨hN,hW,action,hformula,hkernel,_⟩ :=
    eight_six_next_quotient_module_data_local ctx hcenter hlength hcard data.first_commutator
  have hsplit := (eight_six_residual_fixed_decomposition ctx hcenter hlength hcard E hE
    hN hW action hformula hkernel).2.2.2
  have hfixed : QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (twoResidualIn E : Set G) ≤ QAt ctx.Γ ctx.criticalPath.a := by
    by_contra hn
    have hh := eight_six_fixed_core_escape_action_index_le_two ctx hcenter hquot hlength
      hcard previous D L Q hprev hD hL hQ data E hE hAE hn actor ha
    omega
  refine ⟨hfixed,?_⟩
  intro hY
  have hVR : VAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath (by omega) _
  have hVQa : VAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.a := by
    rw [hsplit]
    exact sup_le ((Subgroup.commutator_mono hVR le_rfl).trans hY)
      ((inf_le_inf hVR le_rfl).trans hfixed)
  have hterminal := eight_six_terminal_center_le_next_v ctx.Γ ctx.criticalPath hlength
  have hfirst : ctx.criticalPath.firstStep ∈ Neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  have hcentral := ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core
    ctx.criticalPath.a ctx.criticalPath.firstStep hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (SevenSix.centerAmbient_le_centralizer _))
  exact ctx.commutator_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hcentral.trans (Subgroup.centralizer_le (hterminal.trans hVQa))))

end Stellmacher.SectionEight
