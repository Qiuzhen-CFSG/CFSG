module

public import Stellmacher.SectionEleven.SylowTerminalContext
public import Stellmacher.ExceptionalTypeRealization
public import Stellmacher.SectionNine.CubicLocalAction

/-!
# Central Section Eight terminal realization

These bridges realize every field of the exact (8.6)(a) configuration inside
the ambient group. The graph lives on the generated join, not on the ambient
group. The cubic quotient at the initial vertex makes the initial edge a
two-group; maximality of the restricted Sylow then identifies its intersection.
The normalized edge generates the graph group, so its native join has trivial
two-core. The exceptional-type embedding bridge transports both statements.

The final bridge excludes an actual ambient nonsolvable two-local subgroup.
It explicitly requires the classification disjunction: this module does not
yet assert the missing generated (8.6) classification or the unconditional
`multiple_eight_six_terminal` theorem.

Source: Stellmacher (8.6), the definition following it, and Section Eleven,
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEleven

open Later SectionsFiveToSeven

universe u

variable {H : Type u} [Group H] [Finite H]
  {S0 : Sylow 2 H} {P1 P2 : Subgroup H}

public theorem eight_six_initial_intersection
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two) :
    GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep =
      (S0 : Subgroup H).subgroupOf (P1 ⊔ P2) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := (SectionNine.cubic_local_action_of_sl2Two_quotient
    ctx.Γ ctx.sectionSeven ctx.criticalPath.a hmodel).edge_card
      ctx.criticalPath.firstStep ctx.criticalPath.firstStep_adj
  have hcore : IsPGroup 2 (QAt ctx.Γ ctx.criticalPath.a) := by
    change IsPGroup 2 (ctx.Γ.twoCoreAt ctx.criticalPath.a)
    rw [ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  obtain ⟨exponent, hexponent⟩ := hcore.exists_card_eq
  have hedge : IsPGroup 2
      (↥(GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep)) := by
    apply IsPGroup.of_card (n := exponent + 1)
    change Nat.card _ = 2 * Nat.card _ at hcard
    rw [hcard, hexponent, pow_succ, Nat.mul_comm]
  exact ctx.restrictedSylow.is_maximal' hedge ctx.criticalPath.S_le_edge_stabilizers

public theorem eight_six_initial_join_core
    (ctx : SylowTerminalContext H S0 P1 P2) :
    pCore 2 (↥(GAt ctx.Γ ctx.criticalPath.a ⊔
      GAt ctx.Γ ctx.criticalPath.firstStep)) = ⊥ := by
  have hjoin : GAt ctx.Γ ctx.criticalPath.a ⊔
      GAt ctx.Γ ctx.criticalPath.firstStep = ⊤ := by
    rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
    · exact (congrArg₂ (· ⊔ ·) hedge.1 hedge.2).trans ctx.sectionSeven.generated
    · exact (congrArg₂ (· ⊔ ·) hedge.1 hedge.2).trans
        ((sup_comm _ _).trans ctx.sectionSeven.generated)
  rw [hjoin]
  apply (Subgroup.map_eq_bot_iff_of_injective _
    (f := (Subgroup.topEquiv : (⊤ : Subgroup (P1 ⊔ P2 : Subgroup H)) ≃*
      (P1 ⊔ P2 : Subgroup H)).toMonoidHom) Subgroup.topEquiv.injective).mp
  rw [pCore_map_iso, ctx.sectionSeven.twoCore_eq_bot]

public theorem multiple_eight_six_of_caseA
    (ctx : SylowTerminalContext H S0 P1 P2)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hcase : EightSixCaseATypeData ctx.Γ ctx.criticalPath previous D L Q T) :
    IsOfGTwoTwoDerivedType H := by
  exact isOfGTwoTwoDerivedType_of_subgroup_caseA S0 (P1 ⊔ P2) ctx.sylow_le_join
    ctx.Γ ctx.criticalPath previous D L Q T
    (eight_six_initial_intersection ctx (hcase.local_quotients _))
    (eight_six_initial_join_core ctx) hcase

public theorem multiple_eight_six_of_classification
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hclassification :
      (∃ (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H)),
        EightSixCaseATypeData ctx.Γ ctx.criticalPath previous D L Q T) ∨
      (∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U)) :
    IsOfGTwoTwoDerivedType H := by
  rcases hclassification with ⟨previous, D, L, Q, T, hcase⟩ | ⟨U, hU, hbad⟩
  · exact multiple_eight_six_of_caseA ctx previous D L Q T hcase
  · exact (hbad (hLocal U hU).1).elim

end Stellmacher.SectionEleven
