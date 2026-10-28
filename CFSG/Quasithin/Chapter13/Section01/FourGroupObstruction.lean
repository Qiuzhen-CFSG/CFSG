module

public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction.Automorphisms

/-!
# The four-group obstruction used at the end of §13.1

For p = 5 or 7, a characteristic self-centralizing elementary abelian subgroup
V of order p² prevents a four-group of automorphisms from acting faithfully on
any characteristic quotient H/W with V ≤ W. This is the independent obstruction
used twice on printed p.876 (PDF p.893) of Aschbacher–Smith.

The source notation SL₂(p)/E_(p²) describes an extension with normal elementary
abelian p²-subgroup and quotient SL₂(p). It is not an ordinary quotient of
SL₂(p) by a group of order p². Here H is intended to be L/O₂(L). The §13.1
assembly must supply the actual V, its characteristic and centralizer properties,
the relevant W, and the action constructed from the local geometry. No group
family identification or source theorem is assumed by this adapter.
-/

namespace CFSG.Quasithin.Chapter13.Section01

/-- The genuine odd-characteristic obstruction for the two natural extensions
at the end of §13.1, including further characteristic quotients. -/
public theorem natural_extension_four_group_obstruction
    {H E : Type*} [Group H] [Finite H] [Group E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) {p : ℕ} (hp : p = 5 ∨ p = 7)
    (V W : Subgroup H) [V.Characteristic] [W.Characteristic]
    [IsElementaryAbelian p V] (hV : Nat.card V = p ^ 2)
    (hself : Subgroup.centralizer (V : Set H) ≤ V) (hVW : V ≤ W)
    (ρ : E →* MulAut H) :
    ¬ Function.Injective ((Subgroup.quotientAut W).comp ρ) := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  exact Subgroup.four_group_further_quotient_action_not_injective hE (by omega)
    V W hV hself hVW ρ

end CFSG.Quasithin.Chapter13.Section01
