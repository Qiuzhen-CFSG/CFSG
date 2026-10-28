module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Definitions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# Prime divisors supplied by the distinguished component

Every actual candidate in 13.6.27 has quotient order divisible by 35.
Divisibility through the two-core quotient and the two subgroup inclusions
therefore forces 35 to divide the order of the ambient G. This is the
precise model invariant needed to exclude the field-two endpoints of the
global rank-two alternative in 5.2.3. No order or simplicity theorem for
the remaining Suzuki component is needed in this step.

The candidate orders are existing checked results for the literal ATLAS
J₂, Witt-design M₂₃ and matrix PSL₃(4) carriers. The generic prime divisor
obstruction for the field-two rank-two family remains a separate input
to final assembly, not a conclusion of this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.6.27,
printed p.934, and the global alternative in 5.2.3, printed p.649.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation

/-- Both five and seven divide the actual quotient of every candidate. -/
theorem candidate_thirtyFive_dvd {H : Type*} [Group H] {S K : Subgroup H}
    (hc : Candidate S K) : 35 ∣ Nat.card (K ⧸ pCore 2 K) := by
  rcases hc with hc | hc | ⟨e, _⟩
  · obtain ⟨e⟩ := hc
    rw [Nat.card_congr e.toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    decide
  · obtain ⟨e⟩ := hc
    rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m23_order]
    decide
  · rw [Nat.card_congr e.toEquiv, Matrix.PSL3Four.card_PSL]
    decide

/-- The literal two subgroup inclusions in 13.6.27 transport the quotient
divisor all the way into G, without identifying any quotient with a subgroup. -/
theorem centralizer_candidate_thirtyFive_dvd
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (z : G)
    {K : Subgroup (centralizer ({z} : Set G))}
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K) :
    35 ∣ Nat.card G :=
  (candidate_thirtyFive_dvd hc).trans
    ((pCore 2 K).card_quotient_dvd_card.trans
      (K.card_subgroup_dvd_card.trans (centralizer ({z} : Set G)).card_subgroup_dvd_card))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
