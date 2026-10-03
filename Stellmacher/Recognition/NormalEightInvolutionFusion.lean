module

public import Stellmacher.Recognition.NormalEightSeparatedFusion
public import Stellmacher.Recognition.NormalEightSeparatedCentralizers
public import Stellmacher.Recognition.NormalEightSeparatedCrossAction

/-!
# Reduction of normal-four fusion to the separated local configuration

Failure of fusion separates the unique central involution from the other
involutions of the normal four. Local centralizer control, followed by the
cross-action construction, contradicts that separation by Janko–Thompson 2.1.

The separated local centralizer factorization and cross-action construction
are imported from their dedicated modules. Their hypotheses are discharged
under the N₂ and normal quotient-image assumptions without using fusion.

Source: Janko–Thompson, Math. Z. 113 (1970), §6, first half of printed p.395.
-/

namespace Stellmacher.Recognition.NormalEightInvolutionFusion

open Subgroup NormalEightSeparatedFusion

/-- The local-centralizer and cross-action steps suffice for unconditional
fusion once their premises have been discharged in the separated case. -/
public theorem involutions_fused_of_separated_configuration
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hlocal : ∀ z : S, z ∈ W → z ∈ center S → orderOf z = 2 →
      Separated S W z → CentralizerFactorization S W)
    (hconfiguration : ∀ z : S, z ∈ W → z ∈ center S → orderOf z = 2 →
      Separated S W z → CentralizerFactorization S W → LocalCentralizerControl S W →
        Nonempty (CrossAction (W.map (S : Subgroup G).subtype))) :
    ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G) := by
  classical
  by_contra hnot
  obtain ⟨z, hzW, hzC, hz⟩ := exists_central_involution_mem_four S hno hZ W hW
  have hsep := separated_of_not_fused S hZ W hW z hzW hzC hz hnot
  have hfactor := hlocal z hzW hzC hz hsep
  obtain ⟨c⟩ := hconfiguration z hzW hzC hz hsep hfactor
    (localCentralizerControl_of_factorization S W hfactor)
  exact hnot (c.involutions_fused S W hW)

/-- Unconditional fusion of the involutions in the normal four.

If fusion failed, the central involution supplied by central omega would be
separated from the other involutions.  Lemma 3.1 gives the corresponding
centralizer factorization, and the separated cross-action construction then
produces a configuration whose fixed-point-free actions fuse all four
involutions, contradicting the separation assumption.
-/
public theorem involutions_fused
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal] :
    ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G) := by
  apply involutions_fused_of_separated_configuration S hno hZ W hW
  · intro z hzW hzC hz hsep
    exact NormalEightSeparatedCentralizers.factorization_of_separated
      hns hN S A hA hnonab hZ hno W hW hunique z hzW hzC hz hsep
  · intro z hzW hzC hz hsep hfactor hcontrol
    exact NormalEightSeparatedCrossAction.crossAction_of_separated
      hns hN S A hA hnonab hZ hno W hW hunique z hzW hzC hz hsep
      hfactor hcontrol

end Stellmacher.Recognition.NormalEightInvolutionFusion
