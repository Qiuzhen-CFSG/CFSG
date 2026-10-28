module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteRankOne
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.RootRecovery.RankOneInputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.RankOne
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
/-!
# Finite subfields and the actual simple SL2 maps for triality

The finite fields are embedded in the supplied algebraic closure. The pinned
regular SL2 maps have precisely the positive root parameters and the inverse
source coroot convention used by left weights. These identities are the
common geometric inputs for the central and three-arm finite root charts.
Source: GLS3 2.8.2 and Steinberg 13.3(a).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors
open Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup
open scoped MatrixGroups
namespace Triality.RestrictedWeights.Concrete.RootCharts
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

def fieldEmbedding (n : ℕ) : GaloisField 2 n →+* k := by
  letI : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
  letI : Algebra (ZMod 2) k := ZMod.algebra _ 2
  exact (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 n) (M := k)).toRingHom

def finiteSubfield (n : ℕ) : Subfield k := (fieldEmbedding k n).fieldRange

instance finiteSubfield_finite (n : ℕ) : Finite (finiteSubfield k n) :=
  Finite.of_equiv (GaloisField 2 n) (fieldEmbedding k n).rangeRestrictFieldEquiv.toEquiv

theorem finiteSubfield_card (n : ℕ) (hn : 0<n) : Nat.card (finiteSubfield k n)=2^n := by
  change Nat.card (fieldEmbedding k n).fieldRange=2^n
  rw [Nat.card_congr (fieldEmbedding k n).rangeRestrictFieldEquiv.toEquiv.symm]
  exact GaloisField.card 2 n hn.ne'

theorem finiteSubfield_pow (n : ℕ) (hn : 0<n) (t : finiteSubfield k n) :
    (t : k)^(2^n)=(t : k) := by
  let : Fintype (finiteSubfield k n) := Fintype.ofFinite _
  have h := FiniteField.pow_card t
  rw [← Nat.card_eq_fintype_card, finiteSubfield_card k n hn] at h
  exact congrArg Subtype.val h

def simpleMap (i : Fin 4) : Morphism (slVariety k 2) (groupVariety k) :=
  (RankOne.hasRootMap_simple k i).choose

theorem simpleMap_upper (i : Fin 4) (t : k) :
    (simpleMap k i).onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
      Pinning.rootPoint k (simpleRoot i) t := (RankOne.hasRootMap_simple k i).choose_spec.1 t

theorem simpleMap_lower (i : Fin 4) (t : k) :
    (simpleMap k i).onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)) =
      Pinning.rootPoint k (negativeRoot (simpleRoot i)) t :=
  (RankOne.hasRootMap_simple k i).choose_spec.2 t

private theorem standardDiagonal_eq_binaryCoroot_inv (t : Variety.Point (KMult k)) :
    standardSL2DiagonalMorphism.onPoints t = binarySL2Coroot.onPoints t⁻¹ := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change (slPointEquiv 2 (standardSL2DiagonalMorphism.onPoints t)).val =
    slPointMatrix 2 (binarySL2Coroot.onPoints t⁻¹)
  rw [LeftWeights.RankOne.diagonal_matrix, binarySL2Coroot_matrix, LeftWeights.dPointEquiv_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

local instance geometryTorus (hu : IsUniversalVersion (groupVariety k)) :
    AlgebraicGroup (finiteGeometry k hu).torus.carrierVariety :=
  ClosedSubgroup.carrierAlgebraicGroup _

theorem simpleMap_diagonal (hu : IsUniversalVersion (groupVariety k)) (i : Fin 4)
    (t : Variety.Point (KMult k)) :
    (simpleMap k i).onPoints (standardSL2DiagonalMorphism.onPoints t) =
      (finiteGeometry k hu).torus.includePoint (((finiteGeometry k hu).leftSimpleCoroot i).onPoints t) := by
  rw [standardDiagonal_eq_binaryCoroot_inv,
    RankOne.rootMap_coroot k (simpleMap k i) (simpleMap_upper k i) (simpleMap_lower k i)]
  exact (pinnedRootData_rootCocharacter k (pinnedRootIndex k (simpleRoot i)) t⁻¹).symm
end Triality.RestrictedWeights.Concrete.RootCharts
