module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.TwistedE6.Actors
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.E6.Geometry

/-!
# Faithfulness of the twisted signed chart after the central quotient

Three graph-fixed coroot words invert respectively the extension-field pair
and each fixed-field coordinate. A chart element central in the actual
O^{p′} fixed-point subgroup must therefore have all coordinates zero in odd
characteristic. This proves faithfulness for the literal twisted model's
own central quotient, without using the center of the ambient split group.

Source: Aschbacher–Smith A.2.17, printed p.39; GLS3 §2.6.
-/

@[expose] public noncomputable section
open TwistedE6 TwistedE6.FoldedSubsystem
open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.RankFour
attribute [local instance] Classical.decEq
open ExceptionalSplit.OddRankFour

variable (p : ℕ) [Fact p.Prime] (m : ℕ)

theorem coefficient_two_ne_zero (hp2 : p ≠ 2) : (2 : CoefficientField p m) ≠ 0 := by
  intro hz
  have hd := (CharP.cast_eq_zero_iff (CoefficientField p m) p 2).mp hz
  exact hp2 (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (Fact.out : p.Prime).ne_one)

theorem foldedSignActor_square (i : Fin 4) : foldedSignActor p m i ^ 2 = 1 := by
  apply ambientInclusion_injective p m
  rw [map_pow,map_one,foldedSignActor_coroot]
  have hs (j : Fin 6) : nativeCoroot (CoefficientField p m) j ^ 2 = 1 :=
    ExceptionalSplit.OddRankFour.elementaryCoroot_square _
  have hc (j k : Fin 6) : Commute (nativeCoroot (CoefficientField p m) j)
      (nativeCoroot (CoefficientField p m) k) :=
    ExceptionalSplit.OddRankFour.elementaryCoroot_commute _ _
  fin_cases i
  · change ((nativeCoroot (CoefficientField p m) 0 * nativeCoroot (CoefficientField p m) 5).val)^2=1
    rw [← Subgroup.coe_pow,(hc 0 5).mul_pow,hs,hs,one_mul]
    rfl
  · change ((nativeCoroot (CoefficientField p m) 1 * nativeCoroot (CoefficientField p m) 4).val)^2=1
    rw [← Subgroup.coe_pow,(hc 1 4).mul_pow,hs,hs,one_mul]
    rfl
  · change (nativeCoroot (CoefficientField p m) 2).val^2=1
    rw [← Subgroup.coe_pow,hs]
    rfl
  · change (nativeCoroot (CoefficientField p m) 3).val^2=1
    rw [← Subgroup.coe_pow,hs]
    rfl

def chartModel : Parameters p m →* Model p m := (toModel p m).comp (chartCover p m)

def involution : Model p m := toModel p m (foldedSignActor p m 0)

theorem involution_square : involution p m ^ 2 = 1 := by
  rw [involution,← map_pow,foldedSignActor_square,map_one]


def nativeParameters (a : Parameters p m) : Fin 4 → Multiplicative (CoefficientField p m) :=
  ![a.1,Multiplicative.ofAdd (fieldTwist p m a.1.toAdd),
    Multiplicative.ofAdd (a.2.1.toAdd : CoefficientField p m),
    Multiplicative.ofAdd (a.2.2.toAdd : CoefficientField p m)]

theorem chartCover_native (a : Parameters p m) :
    ambientInclusion p m (chartCover p m a) =
      (E6.chart (CoefficientField p m) (nativeParameters p m a)).val := by
  rw [chartCover_ambient,E6.chart_formula]
  rfl

theorem chartModel_injective (hp2 : p ≠ 2) : Function.Injective (chartModel p m) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have hc : chartCover p m a ∈ Subgroup.center (definingCharacteristicSubgroup p m) :=
    (toModel_eq_one p m _).mp ha
  have he (i : Fin 4) : foldedSignActor p m i * chartCover p m a *
      (foldedSignActor p m i)⁻¹ = chartCover p m a := by
    rw [Subgroup.mem_center_iff.mp hc _,mul_assoc,mul_inv_cancel,mul_one]
  have he' (i : Fin 4) := congrArg (ambientInclusion p m) (he i)
  have hmul (x y : splitCarrier (CoefficientField p m)) : (x*y).val=x.val*y.val := rfl
  have hinv (x : splitCarrier (CoefficientField p m)) : (x⁻¹).val=x.val⁻¹ := rfl
  have hinj := E6.chart_injective (CoefficientField p m) (coefficient_two_ne_zero p m hp2)
  have hpair : ![(nativeParameters p m a 0)⁻¹,(nativeParameters p m a 1)⁻¹,
      nativeParameters p m a 2,nativeParameters p m a 3] = nativeParameters p m a := by
    apply hinj
    rw [← E6.coroot_pair_chart]
    apply Subtype.ext
    have h := he' 1
    simpa only [map_mul,map_inv,chartCover_native,foldedSignActor_coroot,
      Matrix.cons_val,hmul,hinv,nativeCoroot,
      E6.coroot,ExceptionalSplit.OddRankFour.SixNodes.coroot,E6.nodes] using h
  have htwo : ![nativeParameters p m a 0,nativeParameters p m a 1,
      (nativeParameters p m a 2)⁻¹,nativeParameters p m a 3] = nativeParameters p m a := by
    apply hinj
    rw [← E6.coroot_three_chart]
    apply Subtype.ext
    change (E6.coroot (CoefficientField p m) 3).val *
      (E6.chart (CoefficientField p m) (nativeParameters p m a)).val *
      (E6.coroot (CoefficientField p m) 3).val⁻¹ =
      (E6.chart (CoefficientField p m) (nativeParameters p m a)).val
    have h := he' 3
    simpa only [map_mul,map_inv,chartCover_native,foldedSignActor_coroot,
      Matrix.cons_val,hmul,hinv,nativeCoroot,
      E6.coroot,ExceptionalSplit.OddRankFour.SixNodes.coroot,E6.nodes] using h
  have hthree : ![nativeParameters p m a 0,nativeParameters p m a 1,
      nativeParameters p m a 2,(nativeParameters p m a 3)⁻¹] = nativeParameters p m a := by
    apply hinj
    rw [← E6.coroot_two_chart]
    apply Subtype.ext
    change (E6.coroot (CoefficientField p m) 2).val *
      (E6.chart (CoefficientField p m) (nativeParameters p m a)).val *
      (E6.coroot (CoefficientField p m) 2).val⁻¹ =
      (E6.chart (CoefficientField p m) (nativeParameters p m a)).val
    have h := he' 2
    simpa only [map_mul,map_inv,chartCover_native,foldedSignActor_coroot,
      Matrix.cons_val,hmul,hinv,nativeCoroot,
      E6.coroot,ExceptionalSplit.OddRankFour.SixNodes.coroot,E6.nodes] using h
  have hzero (x : CoefficientField p m) (hx : -x=x) : x=0 :=
    (mul_eq_zero.mp ((two_mul x).trans (neg_eq_iff_add_eq_zero.mp hx))).resolve_left
      (coefficient_two_ne_zero p m hp2)
  have h0 : a.1=1 := by
    apply Multiplicative.toAdd.injective
    exact hzero _ (congrArg Multiplicative.toAdd (congrFun hpair 0))
  have h2 : a.2.1=1 := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hzero _ (congrArg Multiplicative.toAdd (congrFun htwo 2))
  have h3 : a.2.2=1 := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hzero _ (congrArg Multiplicative.toAdd (congrFun hthree 3))
  exact Prod.ext h0 (Prod.ext h2 h3)

end TwistedE6.RankFour
