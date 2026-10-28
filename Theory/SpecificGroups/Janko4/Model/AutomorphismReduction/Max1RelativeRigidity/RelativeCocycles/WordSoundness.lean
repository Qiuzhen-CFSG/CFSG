module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.Core
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.RelativeCocycles.Binary
import Mathlib.Tactic.Group

/-!
# Interpreting the finite right cocycle in the actual max1 group

Bit-vector evaluation is the existing faithful mask parametrization of the
canonical elementary kernel. Its XOR and right-conjugation laws identify the
finite word recurrence with the actual displacement `g⁻¹ * phi g`. Inverse
letters use inverse right actions, rather than left conjugation tables.

A word fixing mask three centralizes the actual element `v`. Thus the relative
hypothesis places its displacement on the two-element line `{0,3}`. No finite
constraint or cohomological assertion is assumed in these soundness lemmas.
Source: literal ATLAS `J4G1-max1W1`, through `KernelCount.Relations` and
`Max1Fusion.KernelOrbits.Coordinates`; motivation: GLS3 Table 5.3i.
-/
@[expose] public section
namespace Janko4.Max1RelativeRigidity.RelativeCocycles
open Cardinality Cardinality.KernelCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

def eval (z : V) : M := maskValue matrixA_mul_self matrixB_pow_four z.toNat

lemma eval_zero : eval 0 = 1 :=
  congrArg Subtype.val (maskValue_zero matrixA_mul_self matrixB_pow_four)

lemma eval_three : eval 3 = v := maskValue_three matrixA_mul_self matrixB_pow_four

lemma eval_xor (a b : V) : eval (a ^^^ b) = eval a * eval b := by
  exact congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four a.toNat b.toNat)

lemma eval_injective : Function.Injective eval := by
  intro a b h
  have h' := maskValue_injective (a₁ := ⟨a.toNat, a.isLt⟩)
    (a₂ := ⟨b.toNat, b.isLt⟩) (Subtype.ext h)
  exact BitVec.eq_of_toNat_eq (congrArg Fin.val h')

lemma eval_surjective (e : K) : ∃ a : V, eval a = e := by
  obtain ⟨m, hm⟩ := maskEquiv.surjective e
  exact ⟨BitVec.ofNatLT m.val m.isLt, congrArg Subtype.val hm⟩

lemma eval_inv (a : V) : (eval a)⁻¹ = eval a := by
  apply inv_eq_of_mul_eq_one_right
  rw [← eval_xor, BitVec.xor_self]
  exact eval_zero

lemma eval_actX (a : V) : eval (actX a) = x⁻¹ * eval a * x := by
  rw [eval, actX_toNat]
  exact (right_conj_mask_x matrixA_mul_self matrixB_pow_four a.toNat).symm

lemma eval_actY (a : V) : eval (actY a) = y⁻¹ * eval a * y := by
  rw [eval, actY_toNat]
  exact (right_conj_mask_y matrixA_mul_self matrixB_pow_four a.toNat).symm

open Letter

def letterValue : Letter → M
  | X => x
  | Y => y
  | Xi => x⁻¹
  | Yi => y⁻¹

lemma eval_actLetter (l : Letter) (a : V) :
    eval (actLetter l a) = (letterValue l)⁻¹ * eval a * letterValue l := by
  cases l with
  | X => exact eval_actX a
  | Y => exact eval_actY a
  | Xi =>
    have h := congrArg (fun t : M => x * t * x⁻¹) (eval_actX (actX a))
    rw [actX_sq] at h
    simpa only [actLetter, letterValue, inv_inv, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel, mul_one] using h.symm
  | Yi =>
    have h := congrArg (fun t : M => y * t * y⁻¹) (eval_actY (actY (actY a)))
    rw [actY_cube] at h
    simpa only [actLetter, letterValue, inv_inv, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel, mul_one] using h.symm

lemma delta_inv (phi : MulAut M) (g : M) :
    delta phi g⁻¹ = g * (delta phi g)⁻¹ * g⁻¹ := by
  simp only [delta, map_inv, inv_inv, mul_inv_rev]
  group

lemma eval_deltaLetter (phi : MulAut M) (a b : V)
    (ha : delta phi x = eval a) (hb : delta phi y = eval b) (l : Letter) :
    delta phi (letterValue l) = eval (deltaLetter a b l) := by
  cases l with
  | X => exact ha
  | Y => exact hb
  | Xi =>
    simpa only [letterValue, deltaLetter, actLetter, inv_inv, delta_inv, ha, eval_inv]
      using (eval_actLetter Xi a).symm
  | Yi =>
    simpa only [letterValue, deltaLetter, actLetter, inv_inv, delta_inv, hb, eval_inv]
      using (eval_actLetter Yi b).symm

def wordValue (w : List Letter) : M := (w.map letterValue).prod

lemma eval_wordAct (w : List Letter) (a : V) :
    eval (wordAct w a) = (wordValue w)⁻¹ * eval a * wordValue w := by
  induction w generalizing a with
  | nil => simp [wordAct, wordValue]
  | cons l w ih =>
    change eval (wordAct w (actLetter l a)) = _
    rw [ih, eval_actLetter]
    simp only [wordValue, List.map_cons, List.prod_cons, mul_inv_rev, mul_assoc]

lemma delta_fold (phi : MulAut M) (a b : V)
    (ha : delta phi x = eval a) (hb : delta phi y = eval b)
    (w : List Letter) (g : M) (d : V) (hd : delta phi g = eval d) :
    delta phi (g * wordValue w) =
      eval (w.foldl (fun z l => actLetter l z ^^^ deltaLetter a b l) d) := by
  induction w generalizing g d with
  | nil => simpa only [wordValue, List.map_nil, List.prod_nil, mul_one, List.foldl_nil] using hd
  | cons l w ih =>
    change delta phi (g * (letterValue l * wordValue w)) = _
    rw [← mul_assoc]
    apply ih
    rw [delta_mul, hd, eval_deltaLetter phi a b ha hb, eval_xor, eval_actLetter]

lemma eval_wordDelta (phi : MulAut M) (a b : V)
    (ha : delta phi x = eval a) (hb : delta phi y = eval b) (w : List Letter) :
    delta phi (wordValue w) = eval (wordDelta w a b) := by
  simpa only [one_mul, wordDelta] using delta_fold phi a b ha hb w 1 0
    (by simpa only [delta, map_one, inv_one, one_mul] using eval_zero.symm)

lemma commute_wordValue (w : List Letter) (hw : wordAct w 3 = 3) :
    Commute (wordValue w) v := by
  have h := eval_wordAct w 3
  rw [hw, eval_three] at h
  have h' := congrArg (fun t : M => wordValue w * t) h
  simpa only [Commute, SemiconjBy, mul_assoc, mul_inv_cancel_left] using h'

lemma line_of_mem (a : V) (ha : eval a ∈ Subgroup.zpowers v) : Line a := by
  classical
  have hvne : v ≠ 1 := by
    intro h
    have he : (3 : V) = 0 := eval_injective (by rw [eval_three, eval_zero]; exact h)
    exact (by decide : (3 : V) ≠ 0) he
  have hvorder : orderOf v = 2 := orderOf_eq_prime
    (kernelPair_sq matrixA_mul_self matrixB_pow_four) hvne
  rw [mem_zpowers_iff_mem_range_orderOf, hvorder, Finset.mem_image] at ha
  obtain ⟨n, hn, he⟩ := ha
  have hn' : n = 0 ∨ n = 1 := by have hn2 := Finset.mem_range.mp hn; omega
  rcases hn' with rfl | rfl
  · left
    apply eval_injective
    simpa only [pow_zero, eval_zero] using he.symm
  · right
    apply eval_injective
    simpa only [pow_one, eval_three] using he.symm

lemma relative_word_constraint (phi : MulAut M) (a b : V)
    (ha : delta phi x = eval a) (hb : delta phi y = eval b)
    (hrelative : ∀ h : M, Commute h v → h⁻¹ * phi h ∈ Subgroup.zpowers v)
    (w : List Letter) (hw : wordAct w 3 = 3) : Line (wordDelta w a b) := by
  apply line_of_mem
  rw [← eval_wordDelta phi a b ha hb]
  exact hrelative (wordValue w) (commute_wordValue w hw)

end Janko4.Max1RelativeRigidity.RelativeCocycles
