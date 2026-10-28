module
public import Stellmacher.SectionEight.EightSixLargeIndexSelection
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreContainment
public import Stellmacher.SectionEight.EightSixSelectedActorCostCases

/-!
The actual large-index configuration through the two remaining cost branches
of Stellmacher (8.6). Starting with equation-one data and the predecessor
actor index at least four, retain the real minimizing actor and the selected
E/A0, quotient-dihedral product and geometric witness. The selected fixed
core lies in the initial core, its residual commutator escapes that core,
and the selected cost is four or every outside actor has cost at least eight.

The proof combines the actual minimizing selector, the proved source-(14)
fixed-core and residual conclusions, and the literal cost comparison and
power-of-two split. No classification alternative or raw small-action model
is assumed. This is the common entry to the remaining cases (b) and (c),
printed pp.43–44 of Stellmacher's Lemma 8.6. The local graph is preserved,
so this assembly applies to the generated-group context as well.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_large_index_structure_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup H)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (equation : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup H) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup H)) :
    let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    ∃ actor : H, ∃ E A0 : Subgroup H,
      actor ∈ A ∧ actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      (∀ other : H, other ∈ A → other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other) ∧
      E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep ∧
      Nonempty (QuotientDihedralProduct E (QAt ctx.Γ ctx.criticalPath.firstStep) A0) ∧
      Nonempty (SectionNine.NineThreeGeometricData ctx.Γ
        ctx.criticalPath.firstStep ctx.criticalPath.a A E A0 actor) ∧
      conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
        QAt ctx.Γ ctx.criticalPath.a ∧
      (QAt ctx.Γ ctx.criticalPath.firstStep ⊓ Subgroup.centralizer (twoResidualIn E : Set H) ≤
        QAt ctx.Γ ctx.criticalPath.a) ∧
      (¬ ⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ ≤ QAt ctx.Γ ctx.criticalPath.a) ∧
      (eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4 ∨
        ∀ other : H, other ∈ A → other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
          8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath other) := by
  obtain ⟨actor,E,A0,ha,hout,hmin,hedge,hmodel,⟨geom⟩,hcore⟩ :=
    eight_six_large_index_configuration_local ctx hcenter hquot hlength hcard previous D L Q
      hprev hD hQ equation hlarge
  have hfixed := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength hcard
    previous D L Q hprev hD hL hQ equation E A0 actor geom hcore hedge ha hout hlarge hmin
  have hcases := eight_six_selected_actor_cost_cases ctx hcenter hquot hlength hcard
    previous D L Q hprev equation E A0 actor geom hcore hedge hD hL ha hout hlarge hmin
  exact ⟨actor,E,A0,ha,hout,hmin,hedge,hmodel,⟨geom⟩,hcore,hfixed.1,hfixed.2,hcases⟩

end Stellmacher.SectionEight
