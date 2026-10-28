module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualInvariance.Lifting
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualInvariance.LocalActions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualInvariance.ParabolicAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualInvariance.Uniqueness

/-!
# Residual invariance from the component Sylow action

The actual section-centralizer definition gives trivial action of S ∩ L on
Y_C/O₂(Y_C). Once the component parabolic supplies [Y_L,S ∩ L] = Y_L, the
rank-two shadow identifies both quotient directions and lifts their invariance
through its two-group kernel. Relative C-component uniqueness inside J(I)
then makes S normalize L. No ambient normality of L is used.

The source-facing theorems discharge the moved commutator identity from the
actual marked component parabolic. Their remaining inputs are the earlier local
conclusions 15.3.11–12 and 15.3.14–16, together with [V,Y_L] ≠ 1; only
three-parts of residual orders are required. Geometry.SourceAssembly combines
these results with the second-choice exclusion and the moving-plane geometry.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.23,
paragraph beginning “Therefore [V,Y_L] ≠ 1”, printed p.1128.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.RankTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.ResidualInvariance
variable {G : Type*} [Group G] [Finite G]

/-- The moved direction and the literal fixed section-centralizer direction
are normal in Y₊S. Only the component Sylow commutator identity is additional
to the earlier rank-two local conclusions. -/
theorem component_residuals_normalized (d : LocalData G) (L : Subgroup G)
    (hYL : d.Yplus ≤ normalizer (L : Set G))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hshadow : RankTwoShadow d.Yplus d.S)
    (hL3 : 3 ^ (Nat.card (YL d L)).factorization 3 = 3)
    (hC3 : 3 ^ (Nat.card (YC d L)).factorization 3 = 3)
    (hmove : ⁅YL d L, d.S ⊓ L⁆ = YL d L) :
    d.Yplus ⊔ d.S ≤ normalizer (YL d L : Set G) ∧
      d.Yplus ⊔ d.S ≤ normalizer (YC d L : Set G) := by
  exact rankTwoShadow_normalizes_of_moved_fixed
    (yplus_perfect_of_choice d.choice) h9 (d.T.isPGroup'.to_le inf_le_left)
    (planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice) hshadow
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left)
    ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left)
    (normal_subgroupOf_of_le_normalizer (ComponentIntersection.normalizes_intersectionResidual hYL))
    (normal_subgroupOf_of_le_normalizer (ComponentIntersection.normalizes_centralizerResidual hYL))
    (ComponentIntersection.intersectionResidual_isPPerfect _ _)
    (ComponentIntersection.centralizerResidual_isPPerfect _ _) hL3 hC3 inf_le_left hmove
    (YC_componentSylow_commutator_le_core d L)

/-- The actual point/line component parabolic supplies the moved-residual
identity needed by the rank-two quotient lift.  This is the source-facing
normalization theorem: the quotient marking is the actual map from
`L ⧸ O₂(L)`, and `P` may be either standard parabolic up to an inner marking.
-/
theorem component_residuals_normalized_of_parabolic (d : LocalData G)
    (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (P : Subgroup Matrix.PSL3Two.SL)
    (hP : P = Matrix.PSL3Two.pointParabolicSL ∨
      P = Matrix.PSL3Two.lineParabolicSL)
    (g : Matrix.PSL3Two.SL)
    (hM : ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = P.conjBy g)
    (hYL : d.Yplus ≤ normalizer (L : Set G))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hshadow : RankTwoShadow d.Yplus d.S)
    (hL3 : 3 ^ (Nat.card (YL d L)).factorization 3 = 3)
    (hC3 : 3 ^ (Nat.card (YC d L)).factorization 3 = 3) :
    d.Yplus ⊔ d.S ≤ normalizer (YL d L : Set G) ∧
      d.Yplus ⊔ d.S ≤ normalizer (YC d L : Set G) := by
  apply component_residuals_normalized d L hYL h9 hshadow hL3 hC3
  exact YL_componentSylow_commutator_eq_of_parabolic d L e P hP g hM

/-- The normalization outputs needed by both choices in 15.3.10, including
normalization of the actual relative C-component. The producer of `hmove`
must use the actual component parabolic without assuming these conclusions. -/
theorem residuals_and_component_normalized (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (hYL : d.Yplus ≤ normalizer (c.L : Set G))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hshadow : RankTwoShadow d.Yplus d.S)
    (hL3 : 3 ^ (Nat.card (YL d c.L)).factorization 3 = 3)
    (hC3 : 3 ^ (Nat.card (YC d c.L)).factorization 3 = 3)
    (hcore : c.L.pCoreIn 2 ≤ centralizer (d.V : Set G))
    (hne : ⁅d.V,YL d c.L⁆ ≠ ⊥)
    (hmove : ⁅YL d c.L, d.S ⊓ c.L⁆ = YL d c.L) :
    (d.Yplus ⊔ d.S ≤ normalizer (YL d c.L : Set G)) ∧
      (d.Yplus ⊔ d.S ≤ normalizer (YC d c.L : Set G)) ∧
      d.S ≤ normalizer (c.L : Set G) := by
  obtain ⟨hL,hC⟩ := component_residuals_normalized d c.L hYL h9 hshadow hL3 hC3 hmove
  exact ⟨hL,hC,component_normalized_of_YL d hI c e hcore hne (le_sup_right.trans hL)⟩

/-- The complete source-facing residual invariance statement.  The moved
commutator is discharged from the actual marked component parabolic, after
which the quotient-axis lift and relative C-component uniqueness give both
residual normalizations and `S ≤ N_G(L)`.
-/
theorem residuals_and_component_normalized_of_parabolic
    (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (P : Subgroup Matrix.PSL3Two.SL)
    (hP : P = Matrix.PSL3Two.pointParabolicSL ∨
      P = Matrix.PSL3Two.lineParabolicSL)
    (g : Matrix.PSL3Two.SL)
    (hM : ((YL d c.L ⊔ (d.S ⊓ c.L)).subgroupOf c.L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) = P.conjBy g)
    (hYL : d.Yplus ≤ normalizer (c.L : Set G))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hshadow : RankTwoShadow d.Yplus d.S)
    (hL3 : 3 ^ (Nat.card (YL d c.L)).factorization 3 = 3)
    (hC3 : 3 ^ (Nat.card (YC d c.L)).factorization 3 = 3)
    (hcore : c.L.pCoreIn 2 ≤ centralizer (d.V : Set G))
    (hne : ⁅d.V,YL d c.L⁆ ≠ ⊥) :
    (d.Yplus ⊔ d.S ≤ normalizer (YL d c.L : Set G)) ∧
      (d.Yplus ⊔ d.S ≤ normalizer (YC d c.L : Set G)) ∧
      d.S ≤ normalizer (c.L : Set G) := by
  have hmove := YL_componentSylow_commutator_eq_of_parabolic d c.L e P hP g hM
  exact residuals_and_component_normalized d hI c e hYL h9 hshadow hL3 hC3
    hcore hne hmove

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.ResidualInvariance
end
