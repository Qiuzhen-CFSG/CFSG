module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.OuterAction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ComponentwiseInner
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases

/-!
# Borel and inner-action steps toward 15.3.49(k)

The descendants prove the cubic quotient from the earlier extraspecial
configuration and the local Borel-control argument under noncontainment.
The theorems here derive the actual inner action and nontriviality before
applying the published invariant-projection argument. A collapsed Borel
supplies centerlessness. The componentwise variant combines inner actions
across all commuting factors and requires no outer-order assertion about
their full product.

The source theorem is still incomplete: the B.5.1/B.5.6 model enumeration,
A.3.18 exceptional exclusions, actual Borel identification and solvability,
and the automorphism argument giving B = T₀, defining field F₂, and the
individual outer-order hypotheses below remain to be supplied. These inputs
are not advertised as consequences of the local data in this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1143–1144, proof of 15.3.49(k).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
variable {G : Type*} [Group G] [Finite G]

/-- The terminal containment, with only the centerless and outer-order model
inputs left explicit. The intrinsic cubic quotient and inner action are derived. -/
lemma Y0_le_closure_of_outer_three_free (H M Y V Y0 L T : Subgroup G)
    [Group.IsSolvable (M ⊓ H : Subgroup G)]
    (hsource : ExtraspecialCase M Y V)
    (hY0 : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G)))
    (hgen : H = reducedOvergroup L Y0 T) (hTM : T ≤ M)
    (hθ : theta (M ⊓ H) = Y0)
    (hj : ∀ K : Subgroup G, Group.IsSolvable K → Y0 ⊔ T ≤ K → K ≤ H → K ≤ M ⊓ H)
    (hTY : T ≤ normalizer (Y0 : Set G)) (hcomm : L = ⁅L, Y0⁆)
    (hc : (L.subgroupOf H).IsCComponent)
    (hcenter : center (starImage H (localSpan L T)) = ⊥)
    (hout : ¬ 3 ∣ Nat.card (MulAut.Outer (starImage H (localSpan L T)))) :
    Y0 ≤ localSpan L T := by
  have hYH : Y0 ≤ H := (hθ ▸ theta_le _).trans inf_le_right
  exact Y0_le_closure_of_inner_star_action H M Y0 L T hgen hTM hθ hj
    (hθ ▸ ComponentIntersection.theta_isPPerfect (M ⊓ H))
    (residual_quotient_card_in H M Y V Y0 hsource hY0 hYH) hTY hcomm
    (component_star_nontrivial H L (localSpan L T)
      hc (le_conjugateSpanBy L T))
    hcenter (inner_star_of_outer_three_free H M Y0 L T hgen hθ hcomm hTY hout)

/-- Conditional assembly after the Borel automorphism calculation. The collapsed
Borel gives centerlessness; the actual inner action and cubic quotient are derived.
Neither model input in this theorem is asserted to follow from `SourceSetup`. -/
theorem Y0_le_closure_of_collapsed_borel
    {κ : GroupClass} {H M Y V Y0 L ZS Z A : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)
    (hB : localSpan L T ⊓
      normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) =
        (T : Subgroup G) ⊓ localSpan L T)
    (hout : ¬ 3 ∣ Nat.card (MulAut.Outer (starImage H (localSpan L T)))) :
    Y0 ≤ localSpan L T := by
  let _ := d.solvable
  exact Y0_le_closure_of_outer_three_free H M Y V Y0 L T d.extraspecial d.residual
    d.replacement d.sylow_le d.theta_eq d.solvable_control d.sylow_normalizes
    d.commutator_eq d.component_in_H
    (closure_star_center_eq_bot_of_self_normalizing H L Y0 T d.replacement
      d.commutator_eq d.sylow_normalizes hB) hout

/-- The componentwise form of the conditional assembly preserves every factor of
the closure. The generating family and its model facts remain to be constructed. -/
theorem Y0_le_closure_of_collapsed_borel_and_factors
    {κ : GroupClass} {H M Y V Y0 L ZS Z A : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)
    (hB : localSpan L T ⊓
      normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) =
        (T : Subgroup G) ⊓ localSpan L T)
    (s : Finset (Subgroup (H ⧸ pCore 2 H)))
    (hspan : s.sup id = starImage H (localSpan L T))
    (hcomm : ∀ A ∈ s, ∀ B ∈ s, A ≠ B → A ≤ centralizer (B : Set (H ⧸ pCore 2 H)))
    (hn : ∀ K ∈ s, starImage H Y0 ≤ normalizer (K : Set (H ⧸ pCore 2 H)))
    (hout : ∀ K ∈ s, ¬ 3 ∣ Nat.card (MulAut.Outer K)) :
    Y0 ≤ localSpan L T := by
  let _ := d.solvable
  exact Y0_le_closure_of_inner_star_action H M Y0 L T d.replacement d.sylow_le
    d.theta_eq d.solvable_control (d.theta_eq ▸ ComponentIntersection.theta_isPPerfect _)
    d.cubic_quotient d.sylow_normalizes d.commutator_eq
    (component_star_nontrivial H L (localSpan L T) d.component_in_H (le_conjugateSpanBy L T))
    (closure_star_center_eq_bot_of_self_normalizing H L Y0 T d.replacement
      d.commutator_eq d.sylow_normalizes hB)
    (inner_star_of_factor_outer_three_free H M Y0 (localSpan L T) d.theta_eq
      s hspan hcomm hn hout)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
