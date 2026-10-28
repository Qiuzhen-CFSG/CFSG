module
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.FixedWeyl.BinaryTits
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits
import all Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus.Weyl
import all Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.WeylAction

/-!
# Literal Weyl normalizers of the marked Ree three-torus

Two explicit Weyl words act on the norm-one parameter pair by
`(a,b) ↦ ((a*b)⁻¹,a)` and `(a,b) ↦ (b,a)`. The opposition word inverts
the torus and centralizes the cycle. All three words are fixed by the
same twisted Frobenius used in `ExceptionalTorus`, so the original Lang
conjugator descends their actions to the actual finite Ree carrier.

The coroot-coordinate comparison turns 4-by-4 integral matrix identities
into equalities of actual algebraic F₄ elements through the binary Tits
representation. Four-letter blocks keep the checked integer calculations
small. The torus actions follow from the existing literal diagonal
conjugation theorem. Internal Weyl implementations are intentionally
shared through `import all`, without exposing their private names.

Sources: GLS3 Example 2.6.3 and Table 4.7.3A; Steinberg, Lectures on
Chevalley Groups, Lemma 19. This retains the full scalar three-center.
-/

@[expose] public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix
namespace ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer
open ExceptionalTorus ReeF4.CentralCovers.OddPrimary.Cyclotomic
open ReeF4.BinaryDegree.ExceptionalTensor
open LocalBlockInput.PairRigidity.FixedCollection
open Parabolics.Binary.FixedGeometry
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
noncomputable section

private def coord (v : Vec 4) : Fin 4 → ℝ :=
  ![v 0+v 1, 2*v 0+v 1+v 2, (3*v 0+v 1+v 2+v 3)/2, v 0]

private theorem coord_injective : Function.Injective coord := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  change v 0 + v 1 = w 0 + w 1 at h0
  change 2*v 0 + v 1 + v 2 = 2*w 0 + w 1 + w 2 at h1
  change (3*v 0 + v 1 + v 2 + v 3)/2 = (3*w 0 + w 1 + w 2 + w 3)/2 at h2
  change v 0 = w 0 at h3
  ext i
  fin_cases i
  · exact h3
  · change v 1 = w 1; linarith
  · change v 2 = w 2; linarith
  · change v 3 = w 3; linarith

private theorem reflection_coord (i : Fin 4) (r : F4Chevalley.Root) :
    coord (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      (reflectionMatrix i).map (Int.castRingHom ℝ) *ᵥ coord r.val := by
  have hv : (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      r.val - (typeF4CorootScale (typeF4SimpleRootIndex i) *
        dot r.val (typeF4SimpleRoot i)) • typeF4SimpleRoot i := by
    change typeF4RootPairing.root _ = _
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
      typeF4RootPairing_pairing]
    rfl
  rw [hv, typeF4CorootScale_simpleRoot]
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [coord, reflectionMatrix, typeF4CartanMatrix, typeF4SimpleRoot,
      dot, Matrix.mulVec, Fin.sum_univ_four, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.succ,
      Pi.sub_apply, Pi.smul_apply] <;> ring

private theorem word_coord (l : List (Fin 4)) (r : F4Chevalley.Root) :
    coord (wordAction l r).val = (wordMatrix l).map (Int.castRingHom ℝ) *ᵥ coord r.val := by
  induction l generalizing r with
  | nil => simp [wordAction, wordMatrix]
  | cons i l ih =>
    change coord (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i)
      (wordAction l r)).val = _
    rw [reflection_coord, ih]
    simp only [wordMatrix, List.map_cons, List.prod_cons]
    rw [Matrix.map_mul, Matrix.mulVec_mulVec]

private theorem rootWord_eq_of_wordMatrix_eq {l k : List (Fin 4)}
    (h : wordMatrix l = wordMatrix k) : rootWord l = rootWord k := by
  have hp (r : F4Chevalley.Root) : wordAction l r = wordAction k r := by
    apply Subtype.ext
    apply coord_injective
    rw [word_coord, word_coord, h]
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective
  apply LinearEquiv.toLinearMap_injective
  apply typeF4RootPairing_base.toWeightBasis.ext
  intro i
  simp only [LinearEquiv.coe_coe, RootPairing.Base.toWeightBasis_apply]
  change typeF4RootPairing_base.wordProd (l.map typeF4RootPairing_baseEquiv) •
    typeF4RootPairing.root i =
      typeF4RootPairing_base.wordProd (k.map typeF4RootPairing_baseEquiv) • typeF4RootPairing.root i
  rw [← RootPairing.IntegralGeckConstruction.root_reflectionWord,
    ← RootPairing.IntegralGeckConstruction.root_reflectionWord]
  have hrw (w : List (Fin 4)) (r : F4Chevalley.Root) :
      RootPairing.IntegralGeckConstruction.reflectionWord
        (w.map typeF4RootPairing_baseEquiv) r = wordAction w r := by
    induction w generalizing r with
    | nil => rfl
    | cons j w ih =>
      simp only [List.map_cons, RootPairing.IntegralGeckConstruction.reflectionWord,
        ih, wordAction, List.prod_cons, Equiv.Perm.mul_apply,
        typeF4RootPairing_baseEquiv_val]
  rw [hrw, hrw]
  exact congrArg Subtype.val (hp i)


variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

private theorem wordElement_eq_of_wordMatrix_eq {l k : List (Fin 4)}
    (h : wordMatrix l = wordMatrix k) : wordElement (F := F) l = wordElement k := by
  let f := ReeF4.BinaryDegree.ExceptionalTensor.Classification.coefficientHom F 0
  have hb (w : List (Fin 4)) :
      ReeF4.BinaryDegree.ExceptionalTensor.Classification.splitEmbedding f (simpleWord 0 w) =
        wordElement (F := F) w := by
    simp only [simpleWord, wordElement, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    change _ = simpleWeyl i
    rw [simpleWeyl_eq]
    simp [Parabolics.weylWord, algebraicNElement,
      ReeF4.BinaryDegree.ExceptionalTensor.Classification.splitEmbedding_rootGenerator]
  rw [← hb l, ← hb k]
  exact congrArg _ ((simpleWord_eq_iff_rootWord_eq _ _).mpr
    (rootWord_eq_of_wordMatrix_eq h))

private theorem wordMatrix_append (l k : List (Fin 4)) :
    wordMatrix (l ++ k) = wordMatrix l * wordMatrix k := by
  simp [wordMatrix, List.map_append, List.prod_append]

omit [CharP F 2] in
private theorem wordElement_append (l k : List (Fin 4)) :
    wordElement (F := F) (l ++ k) = wordElement l * wordElement k := by
  simp [wordElement, List.map_append, List.prod_append]

def cycleWord : List (Fin 4) :=
  [0,1,2,1] ++ [0,2,3,2] ++ [1,0,2,1] ++ [2,3,2,1]

private theorem cycle_matrix : wordMatrix cycleWord =
    !![1,-1,0,0; 3,-2,0,0; 2,-1,0,-1; 1,-1,1,-1] := by
  have h0 : wordMatrix [0,1,2,1] = !![1,-1,0,2; 2,-1,0,2; 1,-1,1,1; 0,0,0,1] := by decide
  have h1 : wordMatrix [0,2,3,2] = !![-1,1,0,0; 0,1,0,0; 0,1,0,-1; 0,1,-1,0] := by decide
  have h2 : wordMatrix [1,0,2,1] = !![0,-1,2,0; 1,-2,2,2; 1,-1,1,1; 0,0,0,1] := by decide
  have h3 : wordMatrix [2,3,2,1] = !![1,0,0,0; 1,-1,2,0; 1,-1,2,-1; 1,-1,1,0] := by decide
  change wordMatrix ([0,1,2,1] ++ [0,2,3,2] ++ [1,0,2,1] ++ [2,3,2,1]) = _
  rw [wordMatrix_append, wordMatrix_append, wordMatrix_append, h0, h1, h2, h3]
  decide

private theorem cycle_rev_matrix : wordMatrix (cycleWord.map Fin.revPerm) =
    !![-1,1,-2,2; -1,0,-2,4; 0,0,-2,3; 0,0,-1,1] := by
  have h0 : wordMatrix [3,2,1,2] = !![1,0,0,0; 1,1,-2,2; 1,0,-1,2; 1,0,-1,1] := by decide
  have h1 : wordMatrix [3,1,0,1] = !![0,-1,2,0; -1,0,2,0; 0,0,1,0; 0,0,1,-1] := by decide
  have h2 : wordMatrix [2,3,1,2] = !![1,0,0,0; 1,1,-2,2; 1,1,-2,1; 0,1,-1,0] := by decide
  have h3 : wordMatrix [1,0,1,2] = !![0,1,-2,2; -1,2,-2,2; 0,1,-1,1; 0,0,0,1] := by decide
  change wordMatrix ([3,2,1,2] ++ [3,1,0,1] ++ [2,3,1,2] ++ [1,0,1,2]) = _
  rw [wordMatrix_append, wordMatrix_append, wordMatrix_append, h0, h1, h2, h3]
  decide

def swapWord : List (Fin 4) :=
  [1,2,1,0] ++ [3,2,1,0] ++ [2,1,2,3] ++ [2,1]

private theorem swap_matrix : wordMatrix swapWord =
    !![2,-1,0,0; 3,-2,0,0; 2,-2,1,0; 1,-1,1,-1] := by
  have h0 : wordMatrix [1,2,1,0] = !![-1,1,0,0; -2,1,0,2; -1,0,1,1; 0,0,0,1] := by decide
  have h1 : wordMatrix [3,2,1,0] = !![-1,1,0,0; -1,0,2,0; -1,0,1,1; -1,0,1,0] := by decide
  have h2 : wordMatrix [2,1,2,3] = !![1,0,0,0; 1,1,0,-2; 1,0,1,-2; 0,0,1,-1] := by decide
  have h3 : wordMatrix [2,1] = !![1,0,0,0; 1,-1,2,0; 1,-1,1,1; 0,0,0,1] := by decide
  change wordMatrix ([1,2,1,0] ++ [3,2,1,0] ++ [2,1,2,3] ++ [2,1]) = _
  rw [wordMatrix_append, wordMatrix_append, wordMatrix_append, h0, h1, h2, h3]
  decide

private theorem swap_rev_matrix : wordMatrix (swapWord.map Fin.revPerm) =
    !![-1,1,-2,2; 0,1,-4,4; 0,0,-2,3; 0,0,-1,2] := by
  have h0 : wordMatrix [2,1,2,3] = !![1,0,0,0; 1,1,0,-2; 1,0,1,-2; 0,0,1,-1] := by decide
  have h1 : wordMatrix [0,1,2,3] = !![0,1,0,-2; 1,1,0,-2; 0,1,0,-1; 0,0,1,-1] := by decide
  have h2 : wordMatrix [1,2,1,0] = !![-1,1,0,0; -2,1,0,2; -1,0,1,1; 0,0,0,1] := by decide
  have h3 : wordMatrix [1,2] = !![1,0,0,0; 1,1,-2,2; 0,1,-1,1; 0,0,0,1] := by decide
  change wordMatrix ([2,1,2,3] ++ [0,1,2,3] ++ [1,2,1,0] ++ [1,2]) = _
  rw [wordMatrix_append, wordMatrix_append, wordMatrix_append, h0, h1, h2, h3]
  decide

def oppositionWord : List (Fin 4) :=
  [0,1,2,3] ++ [0,1,2,3] ++ [0,1,2,3] ++ [0,1,2,3] ++ [0,1,2,3] ++ [0,1,2,3]

private theorem opposition_matrix : wordMatrix oppositionWord = -1 := by
  have hc : (wordMatrix [0,1,2,3])^3 = !![1,0,0,-2; 2,1,-2,-2; 1,1,-1,-2; 1,0,0,-1] := by
    have h0 : wordMatrix [0,1,2,3] = !![0,1,0,-2; 1,1,0,-2; 0,1,0,-1; 0,0,1,-1] := by decide
    rw [h0]
    decide
  change wordMatrix ([0,1,2,3] ++ [0,1,2,3] ++ [0,1,2,3] ++ [0,1,2,3] ++ [0,1,2,3] ++ [0,1,2,3]) = _
  simp only [wordMatrix_append]
  have he : wordMatrix [0,1,2,3] * wordMatrix [0,1,2,3] * wordMatrix [0,1,2,3] * wordMatrix [0,1,2,3] * wordMatrix [0,1,2,3] * wordMatrix [0,1,2,3] =
      (wordMatrix [0,1,2,3])^3 * (wordMatrix [0,1,2,3])^3 := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [he, hc]
  decide

private theorem opposition_rev_matrix : wordMatrix (oppositionWord.map Fin.revPerm) = -1 := by
  have hc : (wordMatrix [3,2,1,0])^3 = !![-1,0,0,2; -2,-1,2,2; -1,-1,1,2; -1,0,0,1] := by
    have h0 : wordMatrix [3,2,1,0] = !![-1,1,0,0; -1,0,2,0; -1,0,1,1; -1,0,1,0] := by decide
    rw [h0]
    decide
  change wordMatrix ([3,2,1,0] ++ [3,2,1,0] ++ [3,2,1,0] ++ [3,2,1,0] ++ [3,2,1,0] ++ [3,2,1,0]) = _
  simp only [wordMatrix_append]
  have he : wordMatrix [3,2,1,0] * wordMatrix [3,2,1,0] * wordMatrix [3,2,1,0] * wordMatrix [3,2,1,0] * wordMatrix [3,2,1,0] * wordMatrix [3,2,1,0] =
      (wordMatrix [3,2,1,0])^3 * (wordMatrix [3,2,1,0])^3 := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [he, hc]
  decide


def cycleElement : AlgebraicPoints F := wordElement cycleWord
def swapElement : AlgebraicPoints F := wordElement swapWord
def inverterElement : AlgebraicPoints F := wordElement oppositionWord

 theorem cycle_cube : (cycleElement (F := F))^3 = 1 := by
  have h : wordElement (F := F) (cycleWord ++ cycleWord ++ cycleWord) = wordElement [] := by
    apply wordElement_eq_of_wordMatrix_eq
    rw [wordMatrix_append, wordMatrix_append, cycle_matrix]
    decide
  change wordElement (cycleWord ++ cycleWord ++ cycleWord) = 1 at h
  simpa only [wordElement_append, cycleElement, pow_succ, pow_zero, one_mul] using h

 theorem swap_square : (swapElement (F := F))^2 = 1 := by
  have h : wordElement (F := F) (swapWord ++ swapWord) = wordElement [] := by
    apply wordElement_eq_of_wordMatrix_eq
    rw [wordMatrix_append, swap_matrix]
    decide
  change wordElement (swapWord ++ swapWord) = 1 at h
  simpa only [wordElement_append, swapElement, pow_two] using h

omit [CharP F 2] in
private theorem opposition_word : wordElement (F := F) oppositionWord = opposition := by
  simp only [oppositionWord, wordElement_append]
  simp only [wordElement, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, opposition]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

 theorem inverter_commutes (l : List (Fin 4)) :
    Commute (inverterElement (F := F)) (wordElement l) := by
  change wordElement oppositionWord * wordElement l = wordElement l * wordElement oppositionWord
  rw [← wordElement_append, ← wordElement_append]
  apply wordElement_eq_of_wordMatrix_eq
  rw [wordMatrix_append, wordMatrix_append, opposition_matrix]
  simp

private theorem cycle_base_fixed :
    wordElement (F := F) baseWord * wordElement (cycleWord.map Fin.revPerm) =
      wordElement cycleWord * wordElement baseWord := by
  rw [← wordElement_append, ← wordElement_append]
  apply wordElement_eq_of_wordMatrix_eq
  rw [wordMatrix_append, wordMatrix_append, base_matrix, cycle_rev_matrix, cycle_matrix]
  decide

private theorem swap_base_fixed :
    wordElement (F := F) baseWord * wordElement (swapWord.map Fin.revPerm) =
      wordElement swapWord * wordElement baseWord := by
  rw [← wordElement_append, ← wordElement_append]
  apply wordElement_eq_of_wordMatrix_eq
  rw [wordMatrix_append, wordMatrix_append, base_matrix, swap_rev_matrix, swap_matrix]
  decide

private theorem opposition_base_fixed :
    wordElement (F := F) baseWord * wordElement (oppositionWord.map Fin.revPerm) =
      wordElement oppositionWord * wordElement baseWord := by
  rw [← wordElement_append, ← wordElement_append]
  apply wordElement_eq_of_wordMatrix_eq
  rw [wordMatrix_append, wordMatrix_append, base_matrix, opposition_rev_matrix, opposition_matrix]
  decide

private theorem twist_simpleWeyl (m : ℕ) (i : Fin 4) :
    (algebraicReeTwist m).onPoints (simpleWeyl (F := F) i) = simpleWeyl (Fin.revPerm i) := by
  classical
  have hr (r : F4Chevalley.Root) :
      (algebraicReeTwist m).onPoints (rootPoint r (1 : F)) = rootPoint (exceptionalRootPermutation r) 1 := by
    simpa only [one_pow, ite_self] using algebraicReeTwist_rootAction (F := F) m r 1
  simp only [simpleWeyl, map_mul, CharTwo.neg_eq, hr,
    exceptionalRootPermutation_simple, exceptionalRootPermutation_neg_simple]

 theorem twist_word (m : ℕ) (l : List (Fin 4)) :
    (algebraicReeTwist m).onPoints (wordElement (F := F) l) =
      wordElement (l.map Fin.revPerm) := by
  induction l with
  | nil => simp [wordElement]
  | cons i l ih =>
    simpa only [wordElement, List.map_cons, List.prod_cons, map_mul, twist_simpleWeyl] using
      congrArg (fun g => simpleWeyl (Fin.revPerm i) * g) ih

private theorem twisted_fixed_of_base_fixed (m : ℕ) (l : List (Fin 4))
    (h : wordElement (F := F) baseWord * wordElement (l.map Fin.revPerm) =
      wordElement l * wordElement baseWord) :
    normalizer (F := F) m * (algebraicReeTwist m).onPoints (wordElement l) * (normalizer m)⁻¹ =
      wordElement l := by
  rw [twist_word]
  have hc : Commute (opposition (F := F)) (wordElement l) := by
    simpa only [inverterElement, opposition_word] using inverter_commutes (F := F) l
  apply (mul_inv_eq_iff_eq_mul).mpr
  change (opposition ^ m * wordElement baseWord) * wordElement (l.map Fin.revPerm) =
    wordElement l * (opposition ^ m * wordElement baseWord)
  rw [mul_assoc, h, ← mul_assoc, (hc.pow_left m).eq, mul_assoc]

 theorem cycle_twisted_fixed (m : ℕ) :
    normalizer m * (algebraicReeTwist m).onPoints (cycleElement (F := F)) *
      (normalizer m)⁻¹ = cycleElement :=
  twisted_fixed_of_base_fixed m cycleWord cycle_base_fixed

 theorem swap_twisted_fixed (m : ℕ) :
    normalizer m * (algebraicReeTwist m).onPoints (swapElement (F := F)) *
      (normalizer m)⁻¹ = swapElement :=
  twisted_fixed_of_base_fixed m swapWord swap_base_fixed

 theorem inverter_twisted_fixed (m : ℕ) :
    normalizer m * (algebraicReeTwist m).onPoints (inverterElement (F := F)) *
      (normalizer m)⁻¹ = inverterElement :=
  twisted_fixed_of_base_fixed m oppositionWord opposition_base_fixed

private theorem cycle_lattice {A : Type*} [CommGroup A] (m : ℕ) (a b : A) :
    latticeAction (wordMatrix cycleWord) (coordinates m a b) =
      coordinates m ((a*b)⁻¹) a := by
  rw [cycle_matrix]
  ext i
  fin_cases i <;>
    norm_num [latticeAction, ExceptionalTorus.coordinates, Fin.prod_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ] <;>
    apply Additive.ofMul.injective <;>
    simp only [ofMul_mul, ofMul_pow, ofMul_zpow, ofMul_inv] <;> module

private theorem swap_lattice {A : Type*} [CommGroup A] (m : ℕ) (a b : A) :
    latticeAction (wordMatrix swapWord) (coordinates m a b) = coordinates m b a := by
  rw [swap_matrix]
  ext i
  fin_cases i <;>
    norm_num [latticeAction, ExceptionalTorus.coordinates, Fin.prod_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ] <;>
    apply Additive.ofMul.injective <;>
    simp only [ofMul_mul, ofMul_pow, ofMul_zpow, ofMul_inv] <;> module

omit [CharP F 2] in
theorem cycle_algebraicMap (m : ℕ) (f : QuadraticField m →+* F) (a : Parameters m) :
    cycleElement * algebraicMap m f a * (cycleElement (F := F))⁻¹ =
      algebraicMap m f ((a.1*a.2)⁻¹,a.1) := by
  change wordElement (F := F) cycleWord * diagonal ((ExceptionalTorus.coordinates m
    (normUnitHom m f a.1) (normUnitHom m f a.2))⁻¹) * (wordElement cycleWord)⁻¹ =
      diagonal ((ExceptionalTorus.coordinates m (normUnitHom m f ((a.1*a.2)⁻¹))
        (normUnitHom m f a.1))⁻¹)
  rw [word_conjugation, map_inv, cycle_lattice]
  simp only [map_inv, map_mul]

omit [CharP F 2] in
theorem swap_algebraicMap (m : ℕ) (f : QuadraticField m →+* F) (a : Parameters m) :
    swapElement * algebraicMap m f a * (swapElement (F := F))⁻¹ =
      algebraicMap m f (a.2,a.1) := by
  change wordElement (F := F) swapWord * diagonal ((ExceptionalTorus.coordinates m
    (normUnitHom m f a.1) (normUnitHom m f a.2))⁻¹) * (wordElement swapWord)⁻¹ =
      diagonal ((ExceptionalTorus.coordinates m (normUnitHom m f a.2) (normUnitHom m f a.1))⁻¹)
  rw [word_conjugation, map_inv, swap_lattice]

omit [CharP F 2] in
theorem inverter_algebraicMap (m : ℕ) (f : QuadraticField m →+* F) (a : Parameters m) :
    inverterElement * algebraicMap m f a * (inverterElement (F := F))⁻¹ =
      (algebraicMap m f a)⁻¹ := by
  rw [inverterElement, opposition_word]
  change opposition * diagonal ((ExceptionalTorus.coordinates m (normUnitHom m f a.1)
    (normUnitHom m f a.2))⁻¹) * opposition⁻¹ = _
  rw [show opposition (F := F) = (simpleWeyl 0 * simpleWeyl 1 * simpleWeyl 2 * simpleWeyl 3)^6 from rfl,
    opposition_diagonal, map_inv]
  rfl

end
end ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer
