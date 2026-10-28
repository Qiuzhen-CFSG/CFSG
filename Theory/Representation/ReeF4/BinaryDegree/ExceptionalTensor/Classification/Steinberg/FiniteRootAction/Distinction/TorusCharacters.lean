module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction.SideMarkers
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.CommutatorGeneration.TorusAction
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer.Torus

/-!
# Highest characters of the two actual Ree tori

Pair each short simple coroot with its long partner under the inverse
exceptional field map. The existing fixed-torus words yield literal elements
of the finite Ree model for every nonzero short parameter. Their action on
the ordinary tensor highest vector has exponent equal to the binary digit
sum in the corresponding short-simple column.

Source: Steinberg (1963), 5.1(4) and 12.2.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction
open Theory.AlgebraicGroup StandardRootSystem
open scoped TensorProduct
open Parabolics
open LocalBlockInput.PairRigidity
open ZeroAndMiddle
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def longNode : LargeLocalSeeds.Side → Fin 4 | .suzuki => 1 | .linear => 0
private def shortNode : LargeLocalSeeds.Side → Fin 4 | .suzuki => 2 | .linear => 3
private def pairedUnit (m : ℕ) (s : LargeLocalSeeds.Side) (t : (CoefficientField m)ˣ) : (CoefficientField m)ˣ :=
  Units.map (rootFieldEnd m (typeF4SimpleRootIndex (shortNode s)) : CoefficientField m →* CoefficientField m) t
private def pairedTorusWord (m : ℕ) (s : LargeLocalSeeds.Side) (t : (CoefficientField m)ˣ) : SplitGroup m :=
  torusWord m (typeF4SimpleRootIndex (longNode s)) (pairedUnit m s t) *
    torusWord m (typeF4SimpleRootIndex (shortNode s)) t

private theorem pairedTorusWord_fixed (m : ℕ) (s : LargeLocalSeeds.Side) (t : (CoefficientField m)ˣ) :
    reeTwist m (pairedTorusWord m s t) = pairedTorusWord m s t := by
  cases s
  · have he : pairedTorusWord m .suzuki t = LocalIndices.SuzukiGaussData.torusFactor t := by
      have hs : ¬IsLongRoot (typeF4SimpleRootIndex 2) := by
        intro h
        have hh := (typeF4SimpleRootIndex_mem_pair_iff 2).mp h
        norm_num at hh
      have he : rootFieldEnd m (typeF4SimpleRootIndex 2) = titsEnd m := by
        simp only [rootFieldEnd, if_neg hs]
      change torusWord m _ (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 2)).toMonoidHom t) * _ = _
      rw [he]
      rfl
    rw [he]
    have h := FixedCollection.SeedGeneration.SuzukiNormalizer.torusFactor_fixed (canonicalLocalBlockInput m) t
    simpa only [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply] using h
  · have he : pairedTorusWord m .linear t =
        LargeLocalSeeds.LinearCommutators.endTorusWord m (pairedUnit m .linear t) := by
      have ht : Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0) : CoefficientField m →* CoefficientField m)
          (pairedUnit m .linear t) = t := by
        apply Units.ext
        have hh := RadicalCoordinates.rootFieldEnd_twice m (typeF4SimpleRootIndex 3) t.val
        rw [exceptionalRootPermutation_simple] at hh
        exact hh
      simp only [pairedTorusWord, longNode, shortNode,
        LargeLocalSeeds.LinearCommutators.endTorusWord]
      rw [ht]
    rw [he]
    have h := LargeLocalSeeds.LinearCommutators.endTorusWord_fixed (canonicalLocalBlockInput m)
      (pairedUnit m .linear t)
    simpa only [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply] using h

def sideTorusElement (m : ℕ) (s : LargeLocalSeeds.Side) (t : (CoefficientField m)ˣ) : Model m :=
  ⟨pairedTorusWord m s t, (mem_fixedSubgroup m _).mpr (pairedTorusWord_fixed m s t)⟩

private theorem split_torusWord (m : ℕ) (f : CoefficientField m →+* F)
    (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ) :
    splitEmbedding f (torusWord m r t) = algebraicCorootElement r (Units.map f.toMonoidHom t) := by
  simp only [torusWord, weylWord, algebraicCorootElement, algebraicNElement, map_mul,
    splitEmbedding_rootGenerator, Units.coe_map, map_inv₀, map_one,
    Units.val_one, inv_one, CharTwo.neg_eq, mul_inv_rev, root_inv]
  simp only [mul_assoc]
  rfl

private theorem frobenius_coroot (r : F4Chevalley.Root) (t : Fˣ) :
    Geometry.frobeniusEnd (algebraicCorootElement r t) = algebraicCorootElement r (t^2) := by
  simp only [algebraicCorootElement, algebraicNElement, map_mul, map_inv,
    Geometry.frobeniusEnd_root, Units.val_pow_eq_pow_val, inv_pow,
    Units.val_one, inv_one, one_pow, CharTwo.neg_eq]

private theorem frobenius_pow_coroot (j : ℕ) (r : F4Chevalley.Root) (t : Fˣ) :
    (Geometry.frobeniusEnd ^ j) (algebraicCorootElement r t) = algebraicCorootElement r (t^(2^j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ']
    change Geometry.frobeniusEnd ((Geometry.frobeniusEnd ^ j) _) = _
    rw [ih,frobenius_coroot,←pow_mul,pow_succ]

@[expose] def sideExponent (b : ℕ → BasicWeight) (n : ℕ) (s : LargeLocalSeeds.Side) : ℕ :=
  ∑i∈Finset.range n, 2^i * sideDigit s (b i)

private theorem torus_factor_highest (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (f : CoefficientField m →+* F) (i : ℕ) (s : LargeLocalSeeds.Side) (t : (CoefficientField m)ˣ) :
    ((basicFactor m B i).action.action ((Geometry.frobeniusEnd ^ i)
      (modelEmbedding f (sideTorusElement m s t)))).val (v i) =
      (f t) ^ (2^i * sideDigit s (b i)) • v i := by
  simp only [modelEmbedding, MonoidHom.comp_apply, toSplitGroup_apply, sideTorusElement,
    pairedTorusWord, map_mul, split_torusWord, frobenius_pow_coroot,
    Units.val_mul, Module.End.mul_apply, hv i |>.2.2, map_smul, smul_smul,
    Units.val_pow_eq_pow_val, Units.coe_map]
  cases s <;> simp [longNode, shortNode, basicCoefficient, sideDigit, pow_mul]

theorem sideTorusElement_highest (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (f : CoefficientField m →+* F) (n : ℕ) (s : LargeLocalSeeds.Side) (t : (CoefficientField m)ˣ) :
    ordinaryAction m B f n (sideTorusElement m s t) (highestTensor m B v n) =
      (f t)^sideExponent b n s • highestTensor m B v n := by
  induction n with
  | zero =>
    change (1 : F) = (f t) ^ (∑i∈Finset.range 0, 2^i * sideDigit s (b i)) • (1 : F)
    simp
  | succ n ih =>
    change ordinaryAction m B f n (sideTorusElement m s t) (highestTensor m B v n) ⊗ₜ[F]
      (((basicFactor m B n).action.action ((Geometry.frobeniusEnd ^ n)
        (modelEmbedding f (sideTorusElement m s t)))).val (v n)) = _
    rw [ih,torus_factor_highest m B b v hv f n s t]
    simp only [sideExponent,Finset.sum_range_succ,pow_add,highestTensor]
    exact TensorProduct.smul_tmul_smul _ _ _ _

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction
