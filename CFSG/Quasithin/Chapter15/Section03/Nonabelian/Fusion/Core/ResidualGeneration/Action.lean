module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Action.Centralizer

/-!
# Residual-action consequences for 15.3.59

Starting from the actual actor and module identifications in `RecognizedAction`,
we prove U ≤ K by Singer displacement and extraspecial Frattini lifting.
Simplicity of the actual inner subgroup, triviality of its automorphism
centralizer, and two-perfectness give [K,V] = K. Restriction and quotient
transport of a supplied Sylow subgroup give |T_K*| = 8.

The displacement conclusion of 15.3.53 places V in the inner actors and
supplies a pure natural vector fixed by C_H(V). The source summand swap
then proves C_H(V)* inner. Consequently, once U = Q_H, C_T(V) ≤ K.

The hypotheses are earlier source conclusions through 15.3.58, including
extraspecial U with center Z, V not contained in Q_H, [U,V] ≤ V, and the
order-four image of [U,V] in U/Z. The literal identifications, action-kernel
equality and actual Sylow subgroup are retained. None of the requested
residual conclusions is an input. The full 15.3.59 and the final transfer
equality remain with the parent `ResidualGeneration` assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.51(1), 15.3.53(2), 15.3.55, 15.3.58–59, printed pp.1145–1150.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

variable {G : Type*} [Group G] [Finite G]
variable {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The four residual-action outputs used by the parent calculation of 15.3.59.
The last conclusion is conditional on the parent's later equality U = Q_H. -/
theorem residual_action_consequences (d : RecognizedAction T Z ZS V t)
    [IsExtraspecial 2 (closureU Z ZS)]
    (S : Sylow 2 (centralizerH Z))
    (hS : (S : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T)
    (hUQ : closureU Z ZS ≤ coreQ Z)
    (hcenter : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hVT : V ≤ T) (hVQ : ¬ V ≤ coreQ Z)
    (hdisplacement : ⁅closureU Z ZS, V⁆ ≤ V)
    (hcard : Nat.card (vectorDisplacement Z ZS V) = 4) :
    closureU Z ZS ≤ residualK Z ∧
      ⁅residualK Z, V⁆ = residualK Z ∧
      Nat.card (actorImage Z (residualSylow T Z)) = 8 ∧
      (closureU Z ZS = coreQ Z → T ⊓ centralizer (V : Set G) ≤ residualK Z) := by
  have hTH : T ≤ centralizerH Z := hS ▸ map_subtype_le _
  have hUH : closureU Z ZS ≤ centralizerH Z := hUQ.trans (map_subtype_le _)
  refine ⟨closure_le_residual d hUH hcenter,
    residual_commutator_eq Z V d.actorEquiv (hVT.trans hTH) hVQ,
    residualSylow_actor_card T Z S hS d.actorEquiv, ?_⟩
  intro he
  exact sylow_centralizer_le_residual d hTH hcenter hkernel (by omega)
    (hVT.trans hTH) hVQ hdisplacement he

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
