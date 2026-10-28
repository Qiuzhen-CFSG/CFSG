module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Data
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus.Roots
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Maximality.NormalizerWords
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup.Commutation

/-!
# The literal two A₂ systems and their Weyl transport

The long roots α₀ and −θ and the short roots α₂ and α₃ form the marked
A₂×A₂ subsystem. Explicit reflection words place the exceptional image of
the short pair at the long pair and carry each signed cross-pair from the
orthogonal simple roots α₀, α₂. The actual Tits lifts therefore prove
commutation of the two root-generated factors, including all parameters.
The twelve-letter twist word has the marking required by `SL3Pair`.
Source: GLS3 §§1.12, 2.6.2 and Example 2.6.3.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
open scoped Matrix
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.RestrictedCells
open ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- True is the first simple root, matching the four elementary SL₃ generators. -/
def longRoot (k : Bool) : F4Chevalley.Root :=
  if k then typeF4SimpleRootIndex 0 else Three.Descent.ExceptionalTorus.lowestRoot

def shortRoot (k : Bool) : F4Chevalley.Root :=
  typeF4SimpleRootIndex (if k then 2 else 3)

def signedRoot (s : Bool) (r : F4Chevalley.Root) : F4Chevalley.Root := if s then r else -r

def rootWord (l : List (Fin 4)) (r : F4Chevalley.Root) : F4Chevalley.Root :=
  reflectionWord (P := typeF4RootPairing) (l.map typeF4RootPairing_baseEquiv) r

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

@[simp] theorem rootWord_neg (l : List (Fin 4)) (r : F4Chevalley.Root) :
    rootWord l (-r) = -rootWord l r := reflectionWord_neg _ _

private theorem neg_val (r : F4Chevalley.Root) : (-r).val = -r.val := by
  exact (typeF4RootPairing.root_reflectionPerm r r).trans
    (typeF4RootPairing.reflection_apply_self r)

/-- Carries the dual short pair (α₁,α₀) onto (α₀,−θ). -/
def placementWord : List (Fin 4) := [1,2,0,1,2,3,0,1,2,1,0]

theorem placement_target (k : Bool) :
    rootWord placementWord (exceptionalRootPermutation (shortRoot k)) = longRoot k := by
  cases k <;> simp only [shortRoot, Bool.false_eq_true, ↓reduceIte,
    exceptionalRootPermutation_simple]
  all_goals
    apply Subtype.ext
    ext q
    fin_cases q <;>
      norm_num [rootWord, placementWord, reflectionWord, reflection_val,
        typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        reflectedVector, typeF4SimpleRoot, longRoot,
        Three.Descent.ExceptionalTorus.lowestRoot, typeF4LowestRoot,
        Matrix.cons_val_two, Matrix.cons_val_three, Fin.rev]

/-- Cross-pair transport from the two orthogonal simple roots. -/
def commutingWord : Bool → Bool → Bool → Bool → List (Fin 4)
  | false, false, false, false => [0,1,2,3,2,1,2,1]
  | false, false, false, true => [3,2,0,1,2,3,2,1,2,1]
  | false, false, true, false => [0,1,2,3,1,2,1]
  | false, false, true, true => [3,2,0,1,2,3,1,2,1]
  | false, true, false, false => [2,3,2,0]
  | false, true, false, true => [2,0]
  | false, true, true, false => [2,3,0]
  | false, true, true, true => [0]
  | true, false, false, false => [0,1,2,3,2,1,2,1,0]
  | true, false, false, true => [3,2,0,1,2,3,2,1,2,1,0]
  | true, false, true, false => [0,1,2,3,1,2,1,0]
  | true, false, true, true => [3,2,0,1,2,3,1,2,1,0]
  | true, true, false, false => [2,3,2]
  | true, true, false, true => [2]
  | true, true, true, false => [2,3]
  | true, true, true, true => []

private theorem commutingWord_target_false_false (t l : Bool) :
    rootWord (commutingWord false false t l) (typeF4SimpleRootIndex 0) = signedRoot false (longRoot false) ∧
    rootWord (commutingWord false false t l) (typeF4SimpleRootIndex 2) = signedRoot t (shortRoot l) := by
  cases t <;> cases l <;> constructor
  all_goals
    apply Subtype.ext
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte, neg_val]
    ext q
    fin_cases q <;>
      norm_num [rootWord, commutingWord, reflectionWord, reflection_val,
        typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        reflectedVector, typeF4SimpleRoot, longRoot, shortRoot, signedRoot,
        Three.Descent.ExceptionalTorus.lowestRoot, typeF4LowestRoot, neg_val,
        Matrix.cons_val_two, Matrix.cons_val_three]

private theorem commutingWord_target_false_true (t l : Bool) :
    rootWord (commutingWord false true t l) (typeF4SimpleRootIndex 0) = signedRoot false (longRoot true) ∧
    rootWord (commutingWord false true t l) (typeF4SimpleRootIndex 2) = signedRoot t (shortRoot l) := by
  cases t <;> cases l <;> constructor
  all_goals
    apply Subtype.ext
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte, neg_val]
    ext q
    fin_cases q <;>
      norm_num [rootWord, commutingWord, reflectionWord, reflection_val,
        typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        reflectedVector, typeF4SimpleRoot, longRoot, shortRoot, signedRoot,
        Three.Descent.ExceptionalTorus.lowestRoot, typeF4LowestRoot, neg_val,
        Matrix.cons_val_two, Matrix.cons_val_three]

private theorem commutingWord_target_true_false (t l : Bool) :
    rootWord (commutingWord true false t l) (typeF4SimpleRootIndex 0) = signedRoot true (longRoot false) ∧
    rootWord (commutingWord true false t l) (typeF4SimpleRootIndex 2) = signedRoot t (shortRoot l) := by
  cases t <;> cases l <;> constructor
  all_goals
    apply Subtype.ext
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte, neg_val]
    ext q
    fin_cases q <;>
      norm_num [rootWord, commutingWord, reflectionWord, reflection_val,
        typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        reflectedVector, typeF4SimpleRoot, longRoot, shortRoot, signedRoot,
        Three.Descent.ExceptionalTorus.lowestRoot, typeF4LowestRoot, neg_val,
        Matrix.cons_val_two, Matrix.cons_val_three]

private theorem commutingWord_target_true_true (t l : Bool) :
    rootWord (commutingWord true true t l) (typeF4SimpleRootIndex 0) = signedRoot true (longRoot true) ∧
    rootWord (commutingWord true true t l) (typeF4SimpleRootIndex 2) = signedRoot t (shortRoot l) := by
  cases t <;> cases l <;> constructor
  all_goals
    apply Subtype.ext
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte, neg_val]
    ext q
    fin_cases q <;>
      norm_num [rootWord, commutingWord, reflectionWord, reflection_val,
        typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        reflectedVector, typeF4SimpleRoot, longRoot, shortRoot, signedRoot,
        Three.Descent.ExceptionalTorus.lowestRoot, typeF4LowestRoot, neg_val,
        Matrix.cons_val_two, Matrix.cons_val_three]

theorem commutingWord_target (s k t l : Bool) :
    rootWord (commutingWord s k t l) (typeF4SimpleRootIndex 0) = signedRoot s (longRoot k) ∧
    rootWord (commutingWord s k t l) (typeF4SimpleRootIndex 2) = signedRoot t (shortRoot l) := by
  cases s <;> cases k
  · exact commutingWord_target_false_false t l
  · exact commutingWord_target_false_true t l
  · exact commutingWord_target_true_false t l
  · exact commutingWord_target_true_true t l

/-- Its composition with exceptional duality exchanges the two marked pairs. -/
def twistWord : List (Fin 4) := [1,0,2,1,0,2,1,2,3,2,1,0]

variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

omit [CharP F 2] in
@[simp] theorem literalMatrix_rootPoint (r : F4Chevalley.Root) (t : F) :
    literalMatrix (rootPoint r t) = F4Chevalley.rootCurve r t :=
  literalMatrix_algebraicRoot r t

def wordElement (l : List (Fin 4)) : AlgebraicPoints F :=
  (l.map (simpleWeyl (F := F))).prod

omit [CharP F 2] in
@[simp] theorem literalMatrix_wordElement (l : List (Fin 4)) :
    literalMatrix (wordElement (F := F) l) = titsUnit (l.map typeF4RootPairing_baseEquiv) := by
  induction l with
  | nil => simp [wordElement]
  | cons i l ih =>
    change literalMatrix (simpleWeyl i * wordElement l) = _
    rw [map_mul, ih]
    simp only [simpleWeyl, map_mul, literalMatrix_rootPoint,
      List.map_cons, titsUnit_cons, typeF4RootPairing_baseEquiv_val]

theorem wordElement_root (l : List (Fin 4)) (r : F4Chevalley.Root) (t : F) :
    wordElement l * rootPoint r t * (wordElement l)⁻¹ = rootPoint (rootWord l r) t := by
  apply literalMatrix_injective
  simp only [map_mul, map_inv, literalMatrix_wordElement, literalMatrix_rootPoint]
  change titsUnit _ * F4Chevalley.rootCurve r t * (titsUnit _)⁻¹ =
    F4Chevalley.rootCurve (rootWord l r) t
  induction l with
  | nil => simp [rootWord, reflectionWord]
  | cons i l ih =>
    have hw : titsUnit (S := F) ((i :: l).map typeF4RootPairing_baseEquiv) =
        titsUnit [typeF4RootPairing_baseEquiv i] *
          titsUnit (l.map typeF4RootPairing_baseEquiv) := by
      simp only [List.map_cons, titsUnit_cons, titsUnit_nil, mul_one]
    rw [hw]
    calc
      _ = titsUnit [typeF4RootPairing_baseEquiv i] *
          (titsUnit (l.map typeF4RootPairing_baseEquiv) * F4Chevalley.rootCurve r t *
            (titsUnit (l.map typeF4RootPairing_baseEquiv))⁻¹) *
          (titsUnit [typeF4RootPairing_baseEquiv i])⁻¹ := by group
      _ = _ := by rw [ih]; exact simple_conj _ _ _

omit [CharP F 2] in
private theorem simple_cross_commute (t u : F) :
    Commute (rootPoint (typeF4SimpleRootIndex 0) t)
      (rootPoint (typeF4SimpleRootIndex 2) u) := by
  have hn : typeF4RootPairing_baseEquiv 0 ≠ typeF4RootPairing_baseEquiv 2 :=
    typeF4RootPairing_baseEquiv.injective.ne (by decide)
  have hz : typeF4RootPairing_base.cartanMatrix (typeF4RootPairing_baseEquiv 2)
      (typeF4RootPairing_baseEquiv 0) = 0 := by
    rw [typeF4RootPairing_base_cartan_apply]
    decide
  have hc := RootPairing.SimpleGeckGroup.commute_positive_positive_of_cartan_eq_zero
    (typeF4RootPairing_baseEquiv 0) (typeF4RootPairing_baseEquiv 2) hn hz t u
  have hm := hc.map (RootPairing.SimpleGeckGroup.subgroup typeF4RootPairing_base F).subtype
  apply literalMatrix_injective
  simp only [map_mul, literalMatrix_rootPoint]
  change F4Chevalley.rootCurve (typeF4SimpleRootIndex 0) t *
      F4Chevalley.rootCurve (typeF4SimpleRootIndex 2) u =
    F4Chevalley.rootCurve (typeF4SimpleRootIndex 2) u *
      F4Chevalley.rootCurve (typeF4SimpleRootIndex 0) t
  change Commute (RootPairing.SimpleGeckGroup.positiveUnit _ t)
    (RootPairing.SimpleGeckGroup.positiveUnit _ u) at hm
  change rootCurveUnit (integralChevalleyRootOperators (P := typeF4RootPairing)) (typeF4RootPairing_baseEquiv 0) t *
      rootCurveUnit (integralChevalleyRootOperators (P := typeF4RootPairing)) (typeF4RootPairing_baseEquiv 2) u =
    rootCurveUnit (integralChevalleyRootOperators (P := typeF4RootPairing)) (typeF4RootPairing_baseEquiv 2) u *
      rootCurveUnit (integralChevalleyRootOperators (P := typeF4RootPairing)) (typeF4RootPairing_baseEquiv 0) t
  rw [rootCurveUnit_simple, rootCurveUnit_simple]
  exact hm.eq

/-- Every signed root curve in the first factor commutes with each in the second. -/
theorem cross_root_commute (s k t l : Bool) (a b : F) :
    Commute (rootPoint (signedRoot s (longRoot k)) a)
      (rootPoint (signedRoot t (shortRoot l)) b) := by
  have h := (simple_cross_commute a b).map
    (MulAut.conj (wordElement (F := F) (commutingWord s k t l))).toMonoidHom
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, wordElement_root,
    (commutingWord_target s k t l).1, (commutingWord_target s k t l).2] using h

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
