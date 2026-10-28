module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.CubicLocal
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.CoreCommutators

/-!
# Local regularity from the actual parabolic core order

The embedded parabolic two-core is the two-part of the full panel kernel.
It lies in U and, by relative normality, in U intersect U^s. If its order
is at least the order of this complementary section, the two subgroups
coincide. Thus the entire section lies in the panel kernel. This criterion
uses no perfectness, local-model recognition, or Weyl-order assumption.

The original unitary profile application uses DGS (11.8)(f), printed p.176:
the beta core has order q^7, which is the complementary-section order from
the quadrangle root products. This supplies Fong--Seitz I (2B) at that
endpoint, including q=2, without a separate affine-exclusion premise.
-/

public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
/-- A core large enough to fill the complementary section proves its containment in the full panel kernel. -/
theorem remainder_le_kernel_of_core_card (i : Fin 2)
    (hc : Nat.card (simpleRemainder Q split i) ≤
      Nat.card ((Q.tits.standardParabolic {Q.simple i}).pCoreIn 2)) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  have hcore : (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 =
      LocalCover.radical Q split i := (radical_eq_parabolic_twoCore Q split i).symm
  have hle := QuadrangleStructure.parabolic_core_le_remainder Q split i
    (hcore ▸ (show LocalCover.radical Q split i ≤ split.U from inf_le_left))
  have he := Subgroup.eq_of_le_of_card_ge hle hc
  rw [← he, hcore]
  exact inf_le_right
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
