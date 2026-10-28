module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Assembly
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientOrder.Packed

/-!
# Quotient centralization of the literal forest actors

Right multiplication of packed twelve-dimensional rows computes the actual
quotient images of the signed source words. Kernel reduction checks commutation
on every basis row. The thirteen kernel actors map to one, so this proves the
quotient premise for every forest edge, including the nonzero fibers.

Source: the unchanged ATLAS J4G1-max2W1 matrices and the published `actorWords`;
see FiberCensus/source/README.md and Aschbacher--Smith, refs/quasithin.pdf,
printed pp.64--65, A.6.1--4. No first-row equality in dimension 112 is assumed.
-/

set_option maxRecDepth 10000
open Janko4.Cardinality.LocalInvolutionCensus
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound QuotientOrderCertificate
open Janko4.GeneratorCertificates
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] sourceX sourceY
@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.Quotient

def qletter (i : ℤ) : Vector ℕ 12 :=
  if i = 1 ∨ i = -1 then #v[2533, 3688, 2585, 58, 3283, 649, 4075, 1447, 616, 3160, 2130, 2384]
  else if i = 2 then #v[895, 124, 359, 4005, 2616, 2695, 1446, 24, 2224, 645, 4013, 2327]
  else if i = -2 then #v[749, 3035, 1525, 1032, 1160, 2542, 3225, 1437, 2480, 133, 2989, 2555]
  else Vector.ofFn (fun i => 2^i.val)

def qrow (x : ℕ) : Fin 12 → ZMod 2 := fun i => bit x i.val

def right (v : ℕ) (w : List ℤ) : ℕ :=
  w.foldl (fun x i => QuotientOrderCertificate.packedRow x (qletter i)) v

theorem qletter_spec (i : ℤ) :
    (quotientMap (sourceLetter i)).val = quotientDecode (qletter i) := by
  by_cases h1 : i = 1
  · subst i
    change (quotientMap sourceX).val = _
    rw [quotientMap_sourceX]
    rfl
  by_cases hm1 : i = -1
  · subst i
    change (quotientMap sourceX⁻¹).val = _
    rw [map_inv, quotientMap_sourceX]
    rfl
  by_cases h2 : i = 2
  · subst i
    change (quotientMap sourceY).val = _
    rw [quotientMap_sourceY]
    rfl
  by_cases hm2 : i = -2
  · subst i
    change (quotientMap sourceY⁻¹).val = _
    rw [map_inv, quotientMap_sourceY]
    rfl
  simp only [sourceLetter, h1, hm1, h2, hm2, ↓reduceIte, map_one,
    Units.val_one, qletter, or_self]
  funext a b
  simp [quotientDecode, get_ofFn, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem right_spec (v : ℕ) (w : List ℤ) :
    qrow (right v w) = Matrix.vecMul (qrow v) (quotientMap (sourceWord w)).val := by
  induction w generalizing v with
  | nil => simp [right, sourceWord]
  | cons a w ih =>
    rw [right, List.foldl_cons]
    change qrow (right (QuotientOrderCertificate.packedRow v (qletter a)) w) = _
    rw [ih]
    have he : qrow (QuotientOrderCertificate.packedRow v (qletter a)) =
        Matrix.vecMul (qrow v) (quotientMap (sourceLetter a)).val := by
      rw [qletter_spec]
      funext i
      exact packedRow_spec v (qletter a) i
    rw [he]
    simp only [sourceWord, List.map_cons, List.prod_cons, map_mul, Units.val_mul,
      Matrix.vecMul_vecMul]


def liftWords : Fin 4 → List ℤ :=
  ![[], [1], (List.replicate 7 [1, 2]).flatten,
    (List.replicate 4 ((List.replicate 5 [1, 2]).flatten ++ [2])).flatten]

theorem sourceWord_append (u v : List ℤ) : sourceWord (u ++ v) = sourceWord u * sourceWord v := by
  simp only [sourceWord, List.map_append, List.prod_append]

theorem sourceWord_repeat (w : List ℤ) (n : ℕ) :
    sourceWord (List.replicate n w).flatten = sourceWord w ^ n := by
  induction n with
  | zero => simp [sourceWord]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, sourceWord_append, ih, pow_succ']

theorem sourceWord_xy : sourceWord [1, 2] = sourceX * sourceY := by
  change sourceX * (sourceY * 1) = sourceX * sourceY
  rw [mul_one]
theorem sourceWord_x : sourceWord [1] = sourceX := mul_one _
theorem sourceWord_y : sourceWord [2] = sourceY := mul_one _
theorem sourceWord_nil : sourceWord [] = 1 := rfl

attribute [local irreducible] sourceWord

theorem liftWords_spec (j : Fin 4) : sourceWord (liftWords j) = sourceLift j := by
  fin_cases j
  · exact sourceWord_nil
  · exact sourceWord_x
  · change sourceWord (List.replicate 7 [1, 2]).flatten = (sourceX * sourceY)^7
    rw [sourceWord_repeat, sourceWord_xy]
  · change sourceWord (List.replicate 4 ((List.replicate 5 [1, 2]).flatten ++ [2])).flatten =
      ((sourceX * sourceY)^5 * sourceY)^4
    rw [sourceWord_repeat, sourceWord_append, sourceWord_repeat, sourceWord_xy, sourceWord_y]

theorem qrow_unit (i : Fin 12) : qrow (2^i.val) = (1 : QuotientMatrix) i := by
  funext j
  simp [qrow, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem commute_of_right (u v : List ℤ)
    (h : ∀ i : Fin 12, right (right (2^i.val) u) v = right (right (2^i.val) v) u) :
    Commute (quotientMap (sourceWord u)) (quotientMap (sourceWord v)) := by
  apply Units.ext
  funext i
  have he := congrArg qrow (h i)
  simp only [right_spec, qrow_unit, ← Matrix.mul_apply_eq_vecMul,
    one_mul] at he
  exact he


set_option maxRecDepth 100000 in
private theorem words_commute_check : ∀ (j : Fin 4), ∀ w ∈ actorWords j, ∀ i : Fin 12,
    right (right (2^i.val) (liftWords j)) w = right (right (2^i.val) w) (liftWords j) := by
  decide +kernel

theorem word_commute (j : Fin 4) (w : List ℤ) (hw : w ∈ actorWords j) :
    Commute (quotientMap (sourceLift j)) (quotientMap (sourceWord w)) := by
  rw [← liftWords_spec j]
  exact commute_of_right _ _ (words_commute_check j w hw)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.Quotient

namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest
open Coordinates

theorem quotient_commute_sourceActor (j : Fin 4) (c : sourceSubgroup)
    (hc : c ∈ sourceActors j) : Commute (quotientMap (sourceLift j)) (quotientMap c) := by
  by_cases hj : j = 0
  · subst j
    change Commute (quotientMap 1) _
    rw [map_one]
    exact Commute.one_left _
  rw [sourceActors, if_neg hj, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    rw [map_kernelFactor_eq_one quotientMap quotientMap_seed]
    exact Commute.one_right _
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
    exact Edges.Quotient.word_commute j w hw

/-- The actual quotient condition, with no extra mathematical premise. -/
theorem quotient_commute_actorAt (k : Fin 11) (n : Fin (fiberBound k)) :
    Commute (quotientMap (sourceLift (fiberIndex k))) (quotientMap (actorAt k n.val)) := by
  apply quotient_commute_sourceActor
  rw [actorAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (actorIndex_lt k n), Option.getD_some]
  exact List.getElem_mem _

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest
