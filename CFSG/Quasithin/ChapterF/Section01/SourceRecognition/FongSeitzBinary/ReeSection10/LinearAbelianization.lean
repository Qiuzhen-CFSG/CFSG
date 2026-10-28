module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LinearSquares
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearCharacteristic

/-!
# The binary Omega preimage and the all-parameter characteristic section

In the binary case the quotient by T₁ is the product of the two cyclic
order-four endpoint roots. The derived upper bound therefore forces both
endpoint coordinates of an element whose square is derived to be involutions.
Together with LinearSquares this identifies X₁ as the inverse image of
Omega₁ of the literal abelianization. This argument applies to both binary
branches. It proves characteristicity without needing the additional
noncontainment-branch description of the derived subgroup or its index.

Combining this with the nonbinary Frattini equality makes X₁ characteristic
for every parameter, hence invariant under the actual linear rank-one group.
Source: Fong--Seitz II (1974), printed p.222, before (10.6).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}

/-- At q=2 the two endpoint roots are cyclic of order four. Their square
fibers, and the derived upper bound, identify the characteristic denominator
without assuming which of the two printed derived-subgroup branches holds. -/
theorem binary_X1_eq_squareKernel (c : ReeSixHData Q split n 0) :
    (X1 Q split).subgroupOf (simpleRemainder Q split 0) = linearSquareKernel Q split := by
  apply le_antisymm
  · intro v hv
    exact (mem_map_iff_mem (simpleRemainder Q split 0).subtype_injective).mp
      (X1_le_linearSquareKernel Q split c hv)
  · intro v hv
    have ht := binary_linearDerived_le_T1 Q split c ((mem_linearSquareKernel Q split v).mp hv)
    have hq : QuotientGroup.mk' ((linearInterior Q split c).subgroupOf (simpleRemainder Q split 0)) (v^2) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ((T1_eq_linearInterior Q split c).le ht)
    have hb : linearBoundary Q split c v ^ 2 = 1 := by
      rw [←map_pow]
      change (linearEdgeEquiv Q split c).symm (QuotientGroup.mk' _ (v^2)) = 1
      rw [hq,map_one]
    have ha2 : (linearBoundary Q split c v).1^2 = 1 := congrArg Prod.fst hb
    have hb2 : (linearBoundary Q split c v).2^2 = 1 := congrArg Prod.snd hb
    rw [←linearBarBoundary_kernel Q split c]
    change Prod.map (positiveSuzukiBar Q split c 2) (positiveSuzukiBar Q split c 0)
      (linearBoundary Q split c v) = (1,1)
    apply Prod.ext
    · exact (positiveSuzukiBar_eq_one Q split c 2 _).mpr
        ((positiveSuzuki_square_eq_one_iff_omega Q split c 2 _).mp ha2)
    · exact (positiveSuzukiBar_eq_one Q split c 0 _).mpr
        ((positiveSuzuki_square_eq_one_iff_omega Q split c 0 _).mp hb2)

/-- The source's literal inverse image of Omega₁ of U_s₁/[U_s₁,U_s₁]. -/
theorem binary_X1_eq_omega_preimage (c : ReeSixHData Q split n 0) :
    (X1 Q split).subgroupOf (simpleRemainder Q split 0) =
      (omega₁ (Abelianization (simpleRemainder Q split 0)) (p := 2)).comap Abelianization.of := by
  rw [binary_X1_eq_squareKernel Q split c,linearSquareKernel_eq_omega_preimage]

theorem binary_X1_characteristic (c : ReeSixHData Q split n 0) :
    ((X1 Q split).subgroupOf (simpleRemainder Q split 0)).Characteristic := by
  rw [binary_X1_eq_squareKernel Q split c]
  exact linearSquareKernel_characteristic Q split

/-- The characteristic denominator for every Ree parameter, including m=0. -/
theorem X1_characteristic (c : ReeSixHData Q split n m) :
    ((X1 Q split).subgroupOf (simpleRemainder Q split 0)).Characteristic := by
  by_cases hm : m = 0
  · subst m
    exact binary_X1_characteristic Q split c
  · exact X1_characteristic_of_pos Q split c (by omega)

/-- The complete rank-one group acts on the same literal X₁ quotient. -/
theorem rankOne_normalizes_X1 (c : ReeSixHData Q split n m) :
    rankOne Q split 0 ≤ normalizer (X1 Q split : Set (X ⧸ Q.D)) := by
  let : ((X1 Q split).subgroupOf (simpleRemainder Q split 0)).Characteristic :=
    X1_characteristic Q split c
  have hk := remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
    (ReeSource.linear_normalizer_index c.linearSylow)
  have hh := normalizer_le_normalizer_characteristic_image (simpleRemainder Q split 0)
    ((X1 Q split).subgroupOf (simpleRemainder Q split 0))
  rw [map_subgroupOf_eq_of_le (X1_le_linearRemainder Q split c)] at hh
  exact ((rankOne_le_parabolic Q split 0).trans
    (remainder_parabolic_normalizes Q split 0 hk)).trans hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
