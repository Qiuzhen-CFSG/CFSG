module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction.HighestLine
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylLifts
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.WeylTransport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RankOne

/-!
# Native Ree Weyl markers for zero digit columns

The two actual fixed orbit-Weyl words detect whether a short-simple digit
column vanishes. At zero weight each simple rank-one representative fixes
the highest vector. Otherwise its translated tensor lies in a distinct
integer homogeneous space: the degree deficit is four times the middle
column sum, or the end column sum. Independence of the actual coroot
characters prevents it from being the original highest vector.

Source: Steinberg (1963), 5.1(4) and 12.2; the Weyl-word test gives the
zero-column information used beside finite torus characters.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction
open Theory.AlgebraicGroup StandardRootSystem
open scoped TensorProduct
open Parabolics.Binary.FixedGeometry
open AlgebraicTensor
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

@[expose] def sideElement (m : ℕ) (s : LargeLocalSeeds.Side) : Model m :=
  ⟨simpleWord m (sideWord s), (mem_fixedSubgroup m _).mpr (sideWord_fixed m s)⟩

omit [CharP F 2] in
private theorem normalizerWord_append (l k : List (Fin 4)) :
    EndNode.normalizerWord (F := F) (l++k) = EndNode.normalizerWord k * EndNode.normalizerWord l := by
  induction l with
  | nil => simp [EndNode.normalizerWord]
  | cons i l ih => simp only [List.cons_append, EndNode.normalizerWord, ih, mul_assoc]

omit [CharP F 2] in
private theorem split_simpleWord (m : ℕ) (f : CoefficientField m →+* F) (l : List (Fin 4)) :
    splitEmbedding f (simpleWord m l) = EndNode.normalizerWord l.reverse := by
  induction l with
  | nil => simp [simpleWord, EndNode.normalizerWord]
  | cons i l ih =>
    simp only [simpleWord, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih, List.reverse_cons, normalizerWord_append]
    simp only [EndNode.normalizerWord, one_mul, Parabolics.weylWord, map_mul,
      splitEmbedding_rootGenerator, algebraicNElement, map_one, map_neg, inv_one,
      Units.val_one]

private theorem frobenius_normalizerWord (l : List (Fin 4)) :
    Geometry.frobeniusEnd (EndNode.normalizerWord (F := F) l) = EndNode.normalizerWord l := by
  induction l with
  | nil => simp [EndNode.normalizerWord]
  | cons i l ih =>
    simp only [EndNode.normalizerWord, map_mul, ih, algebraicNElement,
      Geometry.frobeniusEnd_root, Units.val_one, inv_one]
    simp only [CharTwo.neg_eq, one_pow]

private theorem frobenius_pow_normalizerWord (j : ℕ) (l : List (Fin 4)) :
    (Geometry.frobeniusEnd ^ j) (EndNode.normalizerWord (F := F) l) = EndNode.normalizerWord l := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ']
    change Geometry.frobeniusEnd ((Geometry.frobeniusEnd ^ j) _) = _
    rw [ih, frobenius_normalizerWord]

theorem sideElement_action (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)
    (f : CoefficientField m →+* F) (n : ℕ) (s : LargeLocalSeeds.Side) :
    ordinaryAction m B f n (sideElement m s) = tensorMap m B
      (fun i => ((basicFactor m B i).action.action
        (EndNode.normalizerWord (sideWord s).reverse)).val) n := by
  rw [← ordinaryPointAction_restrict]
  simp only [MonoidHom.comp_apply, modelEmbedding, toSplitGroup_apply, sideElement]
  change tensorMap m B (fun i => ((basicFactor m B i).action.action
    ((Geometry.frobeniusEnd ^ i) (splitEmbedding f (simpleWord m (sideWord s))))).val) n = _
  simp only [split_simpleWord, frobenius_pow_normalizerWord]

@[expose] def sideDigit (s : LargeLocalSeeds.Side) (b : BasicWeight) : ℕ :=
  match s with | .suzuki => b.1.val | .linear => b.2.val

private theorem factor_side_zero (B : AlgebraicFactor F) (b : BasicWeight)
    (v : B.Space) (hv : B.IsBasicHighestWeightVector b v)
    (s : LargeLocalSeeds.Side) (hz : sideDigit s b = 0) :
    (B.action.action (EndNode.normalizerWord (sideWord s).reverse)).val v = v := by
  have hfix (i : Fin 4) (hi : basicCoefficient b i = 0) :
      (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1)).val v = v :=
    NegativeCyclicity.simple_weyl_fixed_of_zero B i v
      (hv.2.1 _ (typeF4RootPairing_base.isPos_of_mem_support
        (typeF4RootPairing_baseEquiv i).property))
      (by intro t; simpa only [hi, pow_zero, one_smul] using hv.2.2 i t)
  cases s <;> simp only [sideDigit] at hz
  · have h1 := hfix 1 (by simp [basicCoefficient])
    have h2 := hfix 2 (by simpa [basicCoefficient] using hz)
    simp [sideWord, EndNode.normalizerWord, map_mul, Module.End.mul_apply, h1, h2]
  · have h0 := hfix 0 (by simp [basicCoefficient])
    have h3 := hfix 3 (by simpa [basicCoefficient] using hz)
    simp [sideWord, EndNode.normalizerWord, map_mul, Module.End.mul_apply, h0, h3]

omit [CharP F 2] in
private theorem tensorMap_highest (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)
    (T : ∀i, Module.End F (basicFactor m B i).Space)
    (v : ∀i, (basicFactor m B i).Space) (n : ℕ) :
    tensorMap m B T n (highestTensor m B v n) = highestTensor m B (fun i => T i (v i)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (tensorMap m B T n (highestTensor m B v n)) ⊗ₜ[F] T n (v n) = _
    rw [ih]
    rfl

omit [CharP F 2] in
private theorem highestTensor_congr (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)
    (v w : ∀i, (basicFactor m B i).Space) (n : ℕ)
    (h : ∀i<n, v i = w i) : highestTensor m B v n = highestTensor m B w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change highestTensor m B v n ⊗ₜ[F] v n = highestTensor m B w n ⊗ₜ[F] w n
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

omit [CharP F 2] in
private theorem highest_mem_weight (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)
    (μ : ℕ → EndNode.Weight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, v i ∈ EndNode.corootWeightSpace (basicFactor m B i) (μ i)) (n : ℕ) :
    highestTensor m B v n ∈ tensorWeightSpace m B μ n := by
  induction n with
  | zero => trivial
  | succ n ih => exact Submodule.apply_mem_map₂ _ ih (hv n)

private def sideWeight (s : LargeLocalSeeds.Side) (b : BasicWeight) : EndNode.Weight :=
  ((sideWord s).reverse).foldl (fun μ i => EndNode.reflectWeight i μ)
    (fun j => (basicCoefficient b j : ℤ))

private theorem sideWeight_deficit (s : LargeLocalSeeds.Side) (b : BasicWeight) :
    weightDegree ((fun j => (basicCoefficient b j : ℤ)) - sideWeight s b) =
      (match s with | .suzuki => 4 | .linear => 1) * (sideDigit s b : ℤ) := by
  cases s <;> simp [sideWeight, sideWord, List.reverse_cons, EndNode.reflectWeight,
    typeF4CartanMatrix, weightDegree, basicCoefficient, sideDigit] <;> ring

theorem sideElement_fixes_highest_iff (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (b : ℕ → BasicWeight)
    (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (f : CoefficientField m →+* F) (n : ℕ) (s : LargeLocalSeeds.Side) :
    ordinaryAction m B f n (sideElement m s) (highestTensor m B v n) = highestTensor m B v n ↔
      ∀i<n, sideDigit s (b i) = 0 := by
  rw [sideElement_action, tensorMap_highest]
  constructor
  · intro he
    let d := tensorDeficit (sourceTensorWeights b) (fun i => sideWeight s (b i)) n
    have hm : highestTensor m B v n ∈ tensorDegreeSpace m B (sourceTensorWeights b) n d := by
      rw [← he]
      apply Submodule.mem_iSup_of_mem (fun i => sideWeight s (b i))
      apply Submodule.mem_iSup_of_mem (show tensorDeficit (sourceTensorWeights b) (fun i => sideWeight s (b i)) n = d from rfl)
      apply highest_mem_weight
      intro i
      exact EndNode.normalizerWord_mem_weight _ _
        (EndNode.basicHighestWeightVector_mem_corootWeightSpace (hv i))
    have h0 := highestTensor_mem_degree_zero m B (sourceTensorWeights b) v
      (fun i => EndNode.basicHighestWeightVector_mem_corootWeightSpace (hv i)) n
    have hd : d = 0 := by
      by_contra hn
      have hdis := (tensorDegreeSpace_iSupIndep m B (sourceTensorWeights b) n).pairwiseDisjoint hn
      have hz := hdis.le_bot ⟨hm,h0⟩
      exact highestTensor_ne_zero m B v (fun i => (hv i).1) n hz
    have hd' : (∑i∈Finset.range n, (sideDigit s (b i) : ℤ)) = 0 := by
      have heq : d = (match s with | .suzuki => 4 | .linear => 1) *
          (∑i∈Finset.range n, (sideDigit s (b i) : ℤ)) := by
        change (∑i∈Finset.range n, weightDegree ((fun j => (basicCoefficient (b i) j : ℤ)) - sideWeight s (b i))) = _
        simp only [sideWeight_deficit, Finset.mul_sum]
        cases s <;> rfl
      rw [heq] at hd
      cases s <;> norm_num at hd ⊢ <;> omega
    intro i hi
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Int.natCast_nonneg (sideDigit s (b j)))).mp hd'
      i (Finset.mem_range.mpr hi)
    exact_mod_cast hz
  · intro hz
    apply highestTensor_congr
    intro i hi
    exact factor_side_zero _ _ _ (hv i) s (hz i hi)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction
