module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.Diagram.Words
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.Diagram.Intertwiner
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.RouteComparison


/-!
# Integral signed action of the E6 opposition operator

Assume the opposition reflection word takes each of the six selected simple
roots to the negative of its diagram image. Rational multiplicity one compares
its transported positive operator with a single reflected target operator.
Integral primitivity makes the comparison scalar a sign. Appending the source
reflection gives the corresponding comparison for the negative operator.

The integral sl₂ relation `[e,[e,f]] = -2e` forces these two signs to agree:
transport the relation, cancel the matrix unit, and read a primitive entry of
`e`. The root-reversing matrix then removes the change of polarity. Thus the
published `oppositionUnit` intertwines both simple operators with one sign per
node, over the integers and before specialization to any characteristic.

The literal E7 and E8 applications supply the signed operator premises of
`e7Six_ker_le_of_integral_signed_intertwiner` and its E8 counterpart in the
parent `Diagram` module. The root-action hypothesis is deliberately retained;
the parent must establish it for the selected roots before applying the kernel
criteria.

Sources: GLS3 §1.12, especially 1.12.1h and Remark 1.12.10, and §2.5;
Aschbacher–Smith A.2.17, printed p.39. This is the integral operator step for
the exceptional inclusions, not a standalone proof of A.2.17.
-/

public section
noncomputable section
namespace RootPairing.IntegralGeckConstruction
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma eMatrix_triple (i : b.support) :
    eMatrix i * (eMatrix i * fMatrix i - fMatrix i * eMatrix i) -
        (eMatrix i * fMatrix i - fMatrix i * eMatrix i) * eMatrix i =
      -(eMatrix i + eMatrix i) := by
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ R)
  change (algebraMap ℤ R).mapMatrix _ = (algebraMap ℤ R).mapMatrix _
  simp only [map_mul, map_sub, map_neg, map_add, RingHom.mapMatrix_apply,
    map_eMatrix, map_fMatrix]
  change ⁅RootPairing.GeckConstruction.e i,
    ⁅RootPairing.GeckConstruction.e i, RootPairing.GeckConstruction.f i⁆⁆ = _
  rw [RootPairing.GeckConstruction.lie_e_f_same, ← lie_skew,
    (RootPairing.GeckConstruction.isSl2Triple i).lie_h_e_nsmul, two_nsmul]

private lemma signed_triple {α : Type*} [Fintype α]
    (E F : Matrix α α ℤ) (a d : ℤ) :
    (a • E) * ((a • E) * (d • F) - (d • F) * (a • E)) -
        ((a • E) * (d • F) - (d • F) * (a • E)) * (a • E) =
      (a * a * d) • (E * (E * F - F * E) - (E * F - F * E) * E) := by
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, smul_sub, mul_sub, sub_mul]
  module

private lemma operator_signs_agree
    (C : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)ˣ)
    (i j : b.support) (a d : ℤ) (ha : a ^ 2 = 1)
    (hE : C.val * eMatrix i = (a • eMatrix j) * C.val)
    (hF : C.val * fMatrix i = (d • fMatrix j) * C.val) : a = d := by
  have he : SemiconjBy C.val (eMatrix i) (a • eMatrix j) := hE
  have hf : SemiconjBy C.val (fMatrix i) (d • fMatrix j) := hF
  have hh := (he.mul_right ((he.mul_right hf).sub_right (hf.mul_right he))).sub_right
    (((he.mul_right hf).sub_right (hf.mul_right he)).mul_right he)
  have haa : a * a = 1 := by simpa only [pow_two] using ha
  change C.val * _ = _ * C.val at hh
  rw [eMatrix_triple, signed_triple, haa, one_mul, eMatrix_triple] at hh
  have hcancel : -((a • eMatrix j) + (a • eMatrix j)) =
      d • -(eMatrix j + eMatrix j) := by
    apply C.isUnit.mul_right_cancel
    simpa only [mul_neg, mul_add, hE, neg_mul, add_mul] using hh
  let := P.indexNeg
  have hentry := congrFun (congrFun hcancel (Sum.inl j)) (Sum.inr (-j : ι))
  have hj : eMatrix j (Sum.inl j) (Sum.inr (-j : ι)) = 1 := by simp [eMatrix]
  simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, hj, smul_eq_mul,
    mul_one] at hentry
  omega
end RootPairing.IntegralGeckConstruction

namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
open ReeF4.WordRelations.RouteComparison RootPairing.SimpleGeckGroup
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma oppositionUnit_node_sign
    (j : Fin 6 → b.support) (i : Fin 6)
    (hroot : reflectionWord (P := P) (oppositionWord.map j) (j i : ι) =
      P.reflectionPerm (j (typeE6DiagramPermutation i)) (j (typeE6DiagramPermutation i))) :
    ∃ e : ℤˣ, e ^ 2 = 1 ∧ ∀ s : Bool,
      (oppositionUnit j).val * (simpleFamily (b := b)).dividedPower (s, j i) 1 =
        ((e : ℤ) • (simpleFamily (b := b)).dividedPower
          (s, j (typeE6DiagramPermutation i)) 1) * (oppositionUnit j).val := by
  let w := oppositionWord.map j
  let k := j (typeE6DiagramPermutation i)
  have hr : reflectionWord (P := P) w (j i : ι) = reflectionWord [k] (k : ι) := hroot
  obtain ⟨q, hq⟩ := exists_rat_smul_titsConjugate_of_reflectionWord_eq w [k] (j i) k hr
  obtain ⟨a, ha, hA⟩ :=
    transported_eMatrix_eq_sign_smul_of_rat_proportional w [k] (j i) k q hq
  have hk : transportedMatrix [k] (eMatrix k) = -fMatrix k := by
    simpa only [transportedMatrix, titsWord, titsWordInv_cons, titsWordInv_nil,
      mul_one, one_mul] using titsLift_conj_eMatrix_neg k
  rw [hk, smul_neg, ← neg_smul] at hA
  have hE : (oppositionUnit j).val * eMatrix (j i) =
      ((-a) • eMatrix k) * (oppositionUnit j).val := by
    have h := congrArg (fun A => A * titsWord w) hA
    have hh : titsWord w * eMatrix (j i) = ((-a) • fMatrix k) * titsWord w := by
      simpa only [transportedMatrix, mul_assoc, titsWord_inv_mul, mul_one] using h
    change (omegaMatrix * titsWord w) * eMatrix (j i) =
      ((-a) • eMatrix k) * (omegaMatrix * titsWord w)
    calc
      _ = omegaMatrix * (titsWord w * eMatrix (j i)) := mul_assoc _ _ _
      _ = omegaMatrix * (((-a) • fMatrix k) * titsWord w) := by rw [hh]
      _ = ((-a) • eMatrix k) * (omegaMatrix * titsWord w) := by
        rw [← mul_assoc, mul_smul_comm, omegaMatrix_mul_fMatrix,
          smul_mul_assoc, mul_assoc, smul_mul_assoc]
  have hr' : reflectionWord (P := P) (w ++ [j i]) (j i : ι) =
      reflectionWord (b := b) [] (k : ι) := by
    let := P.indexNeg
    rw [reflectionWord_append_simple_self, hr]
    change -(-(k : ι)) = (k : ι)
    exact neg_neg _
  obtain ⟨q', hq'⟩ :=
    exists_rat_smul_titsConjugate_of_reflectionWord_eq (w ++ [j i]) [] (j i) k hr'
  obtain ⟨d, -, hD⟩ :=
    transported_eMatrix_eq_sign_smul_of_rat_proportional (w ++ [j i]) [] (j i) k q' hq'
  rw [transportedMatrix_append_simple_eMatrix] at hD
  have hD' : transportedMatrix w (fMatrix (j i)) = (-d) • eMatrix k := by
    have h := congrArg Neg.neg hD
    simpa only [neg_neg, transportedMatrix, titsWord, titsWordInv_nil, one_mul,
      mul_one, neg_smul] using h
  have hF : (oppositionUnit j).val * fMatrix (j i) =
      ((-d) • fMatrix k) * (oppositionUnit j).val := by
    have h := congrArg (fun A => A * titsWord w) hD'
    have hh : titsWord w * fMatrix (j i) = ((-d) • eMatrix k) * titsWord w := by
      simpa only [transportedMatrix, mul_assoc, titsWord_inv_mul, mul_one] using h
    change (omegaMatrix * titsWord w) * fMatrix (j i) =
      ((-d) • fMatrix k) * (omegaMatrix * titsWord w)
    calc
      _ = omegaMatrix * (titsWord w * fMatrix (j i)) := mul_assoc _ _ _
      _ = omegaMatrix * (((-d) • eMatrix k) * titsWord w) := by rw [hh]
      _ = ((-d) • fMatrix k) * (omegaMatrix * titsWord w) := by
        rw [← mul_assoc, mul_smul_comm, omegaMatrix_mul_eMatrix,
          smul_mul_assoc, mul_assoc, smul_mul_assoc]
  have hs : -a = -d := operator_signs_agree (oppositionUnit j) (j i) k (-a) (-d)
    (by simpa only [neg_sq] using ha) hE hF
  let e : ℤˣ := ⟨-a, -a, by nlinarith [ha], by nlinarith [ha]⟩
  refine ⟨e, ?_, ?_⟩
  · apply Units.ext
    change (-a) ^ 2 = 1
    simpa only [neg_sq] using ha
  · intro s
    cases s
    · simpa only [simpleFamily, fDividedPower_one, e, hs] using hF
    · simpa only [simpleFamily, eDividedPower_one, e] using hE

/-- Opposition acts on both simple operators with the same integral sign at each node. -/
theorem exists_oppositionUnit_signed_intertwiner
    (j : Fin 6 → b.support)
    (hroot : ∀ i, reflectionWord (P := P) (oppositionWord.map j) (j i : ι) =
      P.reflectionPerm (j (typeE6DiagramPermutation i)) (j (typeE6DiagramPermutation i))) :
    ∃ e : Fin 6 → ℤˣ, (∀ i, e i ^ 2 = 1) ∧ ∀ s : Bool, ∀ i : Fin 6,
      (oppositionUnit j).val * (simpleFamily (b := b)).dividedPower (s, j i) 1 =
        ((e i : ℤ) • (simpleFamily (b := b)).dividedPower
          (s, j (typeE6DiagramPermutation i)) 1) * (oppositionUnit j).val := by
  choose e he h using fun i => oppositionUnit_node_sign j i (hroot i)
  exact ⟨e, he, fun s i => h i s⟩

attribute [local instance] Classical.decEq
local instance operatorActionFintypeE7Roots : Fintype typeE7Roots := Fintype.ofFinite _
local instance operatorActionFintypeE8Roots : Fintype typeE8Roots := Fintype.ofFinite _

/-- The integral operator premise for the literal six-node E7 realization. -/
theorem e7_exists_oppositionUnit_signed_intertwiner
    (hroot : ∀ i, reflectionWord (P := typeE7RootPairing)
        (oppositionWord.map e7Node) (e7Node i : typeE7Roots) =
      typeE7RootPairing.reflectionPerm (e7Node (typeE6DiagramPermutation i))
        (e7Node (typeE6DiagramPermutation i))) :
    ∃ e : Fin 6 → ℤˣ, (∀ i, e i ^ 2 = 1) ∧ ∀ s : Bool, ∀ i : Fin 6,
      (oppositionUnit e7Node).val *
          (simpleFamily (b := typeE7RootPairing_base)).dividedPower (s, e7Node i) 1 =
        ((e i : ℤ) • (simpleFamily (b := typeE7RootPairing_base)).dividedPower
          (s, e7Node (typeE6DiagramPermutation i)) 1) * (oppositionUnit e7Node).val :=
  exists_oppositionUnit_signed_intertwiner e7Node hroot

/-- The integral operator premise for the literal six-node E8 realization. -/
theorem e8_exists_oppositionUnit_signed_intertwiner
    (hroot : ∀ i, reflectionWord (P := typeE8RootPairing)
        (oppositionWord.map e8Node) (e8Node i : typeE8Roots) =
      typeE8RootPairing.reflectionPerm (e8Node (typeE6DiagramPermutation i))
        (e8Node (typeE6DiagramPermutation i))) :
    ∃ e : Fin 6 → ℤˣ, (∀ i, e i ^ 2 = 1) ∧ ∀ s : Bool, ∀ i : Fin 6,
      (oppositionUnit e8Node).val *
          (simpleFamily (b := typeE8RootPairing_base)).dividedPower (s, e8Node i) 1 =
        ((e i : ℤ) • (simpleFamily (b := typeE8RootPairing_base)).dividedPower
          (s, e8Node (typeE6DiagramPermutation i)) 1) * (oppositionUnit e8Node).val :=
  exists_oppositionUnit_signed_intertwiner e8Node hroot
end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram
