module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Transfer
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Omega
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Assembly

/-!
# Radical Frattini and quaternion actions

The assembled actions prove irreducibility for T on the radical Frattini
quotient and for N_{L₀}(P) on each Sylow complement's Frattini quotient.
The actual action induced by T ∩ L₀ contains Q₈, so Aut_T(P) is noncyclic.
These results use the full A.3.6 implication and the local-family hypotheses;
T-invariance of L₀ is supplied separately where needed.

The general normalizer reduction below remains available for other proved
component omega actions. The source-theorem owners retain the remaining
clauses of 1.3.3 and 1.3.8 and their final assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, pp.509, 513–514.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G]

/-- A proved component action on its omega quotient gives the action of the
local normalizer on every Sylow complement's Frattini quotient. -/
theorem XiP_normalizer_irreducible_of_omega {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (L₀ : Subgroup G)
    (hq : IsPGroup p (XiQuotient (XiP p L₀)))
    (hi : ∀ A : Subgroup (omegaCore p (XiQuotient L₀) ⧸ frattini (omegaCore p (XiQuotient L₀))),
      (∀ g : XiQuotient L₀, ∀ a ∈ A, omegaFrattiniAction p (XiQuotient L₀) g a ∈ A) →
      A = ⊥ ∨ A = ⊤)
    (P : Sylow p (XiP p L₀)) :
    let P₀ := (P : Subgroup (XiP p L₀)).map (XiP p L₀).subtype
    ∀ A : Subgroup (P₀ ⧸ frattini P₀),
      (∀ g : (L₀ ⊓ normalizer P₀ : Subgroup G), ∀ a ∈ A,
        frattiniConjugationAction (L₀ ⊓ normalizer P₀) P₀ inf_le_right g a ∈ A) →
      A = ⊥ ∨ A = ⊤ := by
  apply normalizer_irreducible (XiP_invariant p L₀.le_normalizer)
    ((pCoreIn_le 2 (XiP p L₀)).trans (XiP_le p L₀)) _ ho hq P
  intro B hB
  let e := xiPFrattiniEquivCore ho L₀
  have hiB : ∀ g : XiQuotient L₀, ∀ a ∈ B.map e.toMonoidHom,
      omegaFrattiniAction p (XiQuotient L₀) g a ∈ B.map e.toMonoidHom := by
    intro g a ha
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L₀) g
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨xiFrattiniAction L₀ (XiP p L₀) (XiP_invariant p L₀.le_normalizer) k b,
      hB k b hb, xiPFrattiniEquivCore_equivariant ho L₀ k b⟩
  rcases hi (B.map e.toMonoidHom) hiB with hb | ht
  · exact Or.inl ((B.map_eq_bot_iff_of_injective e.injective).mp hb)
  · right
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective e.toMonoidHom e.surjective]
    exact ht

end CFSG.Quasithin.Chapter1.RadicalActions
