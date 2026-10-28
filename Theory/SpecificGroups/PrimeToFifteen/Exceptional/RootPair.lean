module
public import Theory.SpecificGroups.LieType.ExceptionalSplit.RootFaithfulness
public import Theory.AlgebraicGroup.RootSystems.IntegralTitsCoherence
import all Theory.AlgebraicGroup.RootSystems.IntegralTitsCoherence
public import Mathlib.GroupTheory.OrderOfElement
/-!
# Cubic elements from one pair of opposite root curves

The two parameter-one signed simple roots satisfy the braid relation, and
 their Tits word has fourth power one. The square of their product has cube
one and cannot be central: centrality would identify the two root elements.
Thus any matrix subgroup containing the pair has a cubic in its quotient by
its center. This applies to both split and graph-field exceptional models.

The integral cancellation body is read through a private `import all`; its
public interface is unchanged. Source: Steinberg's rank-one relations in
*Lectures on Chevalley Groups*, Section 3; GLS3 Sections 2.1–2.3.
-/
public section
open Matrix
namespace Theory.GroupTheory.RootPairCubic
variable {G : Type*} [Group G]
theorem cubic_of_braid (a b : G) (hbraid : a*b*a = b*a*b)
    (hfour : (a*b*a)^4 = 1) : ((a*b)^2)^3 = 1 := by
  have hthree : (a*b)^3 = (a*b*a)^2 := by
    calc
      (a*b)^3 = (a*b*a)*(b*a*b) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = (a*b*a)^2 := by rw [← hbraid]; simp only [pow_two]
  rw [← pow_mul, Nat.mul_comm 2 3, pow_mul, hthree, ← pow_mul]
  exact hfour

theorem not_central_of_braid (a b : G) (hbraid : a*b*a = b*a*b)
    (hne : a ≠ b) : (a*b)^2 ∉ Subgroup.center G := by
  intro hc
  have hcomm := Subgroup.mem_center_iff.mp hc b
  have htransport : (a*b)^2*b = a*(a*b)^2 := by
    calc
      (a*b)^2*b = a*(b*a*b)*b := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = a*(a*b*a)*b := by rw [hbraid]
      _ = a*(a*b)^2 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  apply hne
  exact mul_right_cancel (htransport.symm.trans hcomm.symm)

theorem three_dvd_center_quotient (a b : G) (hbraid : a*b*a = b*a*b)
    (hfour : (a*b*a)^4 = 1) (hne : a ≠ b) :
    3 ∣ Nat.card (G ⧸ Subgroup.center G) := by
  let q := QuotientGroup.mk' (Subgroup.center G)
  have hc : q ((a*b)^2)^3 = 1 := by
    rw [← map_pow, cubic_of_braid a b hbraid hfour, map_one]
  have hn : q ((a*b)^2) ≠ 1 := by
    intro h
    exact not_central_of_braid a b hbraid hne ((QuotientGroup.eq_one_iff _).mp h)
  have ho : orderOf (q ((a*b)^2)) = 3 := orderOf_eq_prime hc hn
  rw [← ho]
  exact orderOf_dvd_natCard (q ((a*b)^2))
end Theory.GroupTheory.RootPairCubic
namespace RootPairing.SimpleGeckGroup.ThreeDivisibility
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {F : Type*} [Field F]
private theorem specialize_e (i : b.support) (t : ℤ) :
    specializeMatrix (S := F) (eUnipotent i t) = positiveMatrix i (t : F) := by
  ext j k
  simp only [specializeMatrix, eUnipotent, positiveMatrix_formula, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
    Int.cast_add, Int.cast_mul, Int.cast_pow]
  simp [Matrix.one_apply]
private theorem specialize_f (i : b.support) (t : ℤ) :
    specializeMatrix (S := F) (fUnipotent i t) = negativeMatrix i (t : F) := by
  ext j k
  simp only [specializeMatrix, fUnipotent, negativeMatrix_formula, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
    Int.cast_add, Int.cast_mul, Int.cast_pow]
  simp [Matrix.one_apply]

theorem braid (i : b.support) :
    positiveUnit i (1 : F) * negativeUnit i (-1) * positiveUnit i 1 =
      negativeUnit i (-1) * positiveUnit i 1 * negativeUnit i (-1) := by
  let a := positiveUnit i (1 : F)
  let c := negativeUnit i (-1 : F)
  have hw : rootCurveTitsWord (S := F) [i] = a*c*a := by
    simp [rootCurveTitsWord_cons, a, c]
  have hc : rootCurveTitsWord (S := F) [i] * a = c * rootCurveTitsWord [i] := by
    apply Units.ext
    change specializeMatrix (titsWord [i]) * positiveMatrix i (1 : F) =
      negativeMatrix i (-1 : F) * specializeMatrix (titsWord [i])
    have h := congrArg (specializeMatrix (S := F)) (titsLift_mul_eUnipotent i 1)
    simpa [specializeMatrix_mul, specialize_e, specialize_f, titsWord] using h
  rw [hw] at hc
  exact mul_right_cancel (show (a*c*a)*a = (c*a*c)*a by simpa [mul_assoc] using hc)

theorem fourth (i : b.support) :
    (positiveUnit i (1 : F) * negativeUnit i (-1) * positiveUnit i 1)^4 = 1 := by
  have hw : rootCurveTitsWord (S := F) [i] =
      positiveUnit i 1 * negativeUnit i (-1) * positiveUnit i 1 := by
    simp [rootCurveTitsWord_cons]
  rw [← hw]
  apply Units.ext
  change specializeMatrix (titsWord [i]) ^ 4 = 1
  have h := congrArg (specializeMatrix (S := F)) (titsCancellation_mul_self i)
  simpa only [titsCancellation, specializeMatrix_mul, specializeMatrix_one,
    titsWord, Matrix.mul_one, show (4 : ℕ) = 2*2 from rfl, pow_mul, pow_two] using h

theorem distinct (i : b.support) : positiveUnit i (1 : F) ≠ negativeUnit i (-1) := by
  let := P.indexNeg
  intro h
  have hh := congrArg (fun x => x.val (Sum.inl i) (Sum.inr (-i : ι))) h
  have hp := ExceptionalSplit.TheoremDRootNormalizer.simpleRoot_entry (F := F) i 1
  rw [rootCurveUnit_simple, positiveUnit_val] at hp
  have hn : negativeMatrix i (-1 : F) (Sum.inl i) (Sum.inr (-i : ι)) = 0 := by
    simp [negativeMatrix_formula, fDividedPower, Matrix.mul_apply,
      omegaMatrix, eDividedPower, eMatrix, Matrix.one_apply, P.ne_neg i,
      -RootPairing.indexNeg_neg]
  change positiveMatrix i (1 : F) _ _ = negativeMatrix i (-1 : F) _ _ at hh
  exact one_ne_zero (hp.symm.trans (hh.trans hn))

theorem three_dvd_subgroup_center_quotient (H : Subgroup (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ)
    (i : b.support) (ha : positiveUnit i (1 : F) ∈ H)
    (hb : negativeUnit i (-1 : F) ∈ H) :
    3 ∣ Nat.card (H ⧸ Subgroup.center H) := by
  apply Theory.GroupTheory.RootPairCubic.three_dvd_center_quotient (⟨_,ha⟩ : H) (⟨_,hb⟩ : H)
  · apply Subtype.ext
    exact braid i
  · apply Subtype.ext
    exact fourth i
  · intro h
    exact distinct i (congrArg Subtype.val h)
/-- The same root-pair criterion for a faithfully represented central cover. -/
theorem three_dvd_center_quotient_of_injective
    {G : Type*} [Group G]
    (f : G →* (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ)
    (hf : Function.Injective f) (i : b.support) (a c : G)
    (ha : f a = positiveUnit i 1) (hc : f c = negativeUnit i (-1)) :
    3 ∣ Nat.card (G ⧸ Subgroup.center G) := by
  apply Theory.GroupTheory.RootPairCubic.three_dvd_center_quotient a c
  · apply hf
    simpa only [map_mul, ha, hc] using braid (F := F) i
  · apply hf
    simpa only [map_pow, map_mul, map_one, ha, hc] using fourth (F := F) i
  · intro h
    exact distinct i (ha.symm.trans ((congrArg f h).trans hc))

end RootPairing.SimpleGeckGroup.ThreeDivisibility
