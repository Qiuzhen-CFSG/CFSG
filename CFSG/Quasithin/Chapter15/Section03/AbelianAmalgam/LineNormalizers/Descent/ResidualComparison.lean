module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.ResidualComparison.Products

/-!
# Residual comparison and centralizer collapse in 15.3.67

The prime-to-six generators, the three-coset action and the compatible
orthogonal action give the common residual of the original `G_E`,
`C_G(V)` and `M`. Its relative normality in both overgroups and the
characteristic-two obstruction force it to be trivial.

`centralizer_and_whole_product` then proves `C_G(V) = C_T(V)` and the
literal product `M = Y T`. `line_product_of_marked_action` proves
`M_E = Y_E T_E` using the actual marked action and its centralizer kernel.
`line_product_of_original_sylow` supplies that marked input from the
earlier Sylow promotion in the original line normalizer. These are
conditional descent steps; the parent source-theorem assembly owns the
preceding local, action, index and Sylow hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of Lemma 15.3.67, printed p.1154 (PDF p.1171).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
variable {G : Type*} [Group G] [Finite G]

/-- The full common-residual assertion, with normality relative to the original overgroups. -/
theorem residual_comparison (M V E : Subgroup G) (hEV : E ≤ V)
    (hNM : normalizer (V : Set G) ≤ M) (d : NaturalOrthogonalAction M V)
    (hi : (lineM M E).relIndex (lineNormalizer E) = 3)
    (hM : IsMaximalTwoLocal M)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hout : ¬ lineNormalizer E ≤ M) :
    twoThreeResidual (lineNormalizer E) = twoThreeResidual (centralizer (V : Set G)) ∧
      twoThreeResidual (centralizer (V : Set G)) = twoThreeResidual M ∧
      ((twoThreeResidual (lineNormalizer E)).subgroupOf M).Normal ∧
      ((twoThreeResidual (lineNormalizer E)).subgroupOf (lineNormalizer E)).Normal ∧
      twoThreeResidual (lineNormalizer E) = ⊥ ∧
      twoThreeResidual (centralizer (V : Set G)) = ⊥ ∧ twoThreeResidual M = ⊥ := by
  obtain ⟨heG, heM⟩ := residual_equalities M V E hEV hNM d hi
  have hn := (common_residual_normal M V E hEV hNM d hi).1
  have hr := common_residual_eq_bot M V E hEV hNM d hi hM hchar hout
  refine ⟨heG, heM, ?_, twoThreeResidual_normal _, heG.trans hr, hr, heM.symm.trans hr⟩
  rwa [heG]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
