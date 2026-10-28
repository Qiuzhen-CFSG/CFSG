module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions
import Mathlib.Tactic.Abel

/-!
# Counting reduction for centers in the signed extension

Commutation and the square bound embed a subgroup into explicit finite sets.
The mixed set also retains commutation modulo the sign in both the actor and
vector coordinates. These are consequences of the proved elementary image,
not assumptions about a central-product presentation. If the actor image is
trivial, order 64 forces the entire Clifford radical and determines its center.

The remaining two finite estimates are assembled in the parent `Center` module.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.2(6a),
printed pp.410 and 412 (PDF pp.421 and 423).
-/

@[expose] public section
open Subgroup
namespace EvenCliffordSix.SplitExtension.ElementaryRestrictions

/-- Squaring retains exactly the involution condition on the actor and its
fixed-vector condition; the sign coordinate imposes no further restriction. -/
theorem square_mem_sign_iff (x : SplitExtension) :
    x ^ 2 ∈ sign ↔ x.right ^ 2 = 1 ∧
      permuteVector x.right.val x.left.vector = x.left.vector := by
  have hself : x.left.vector + x.left.vector = 0 := by
    apply Subtype.ext
    funext i
    exact CharTwo.add_self_eq_zero _
  have hvec : x.left.vector + permuteVector x.right.val x.left.vector = 0 ↔
      permuteVector x.right.val x.left.vector = x.left.vector := by
    constructor
    · intro h
      exact add_left_cancel (h.trans hself.symm)
    · intro h
      rw [h]
      exact hself
  rw [mem_sign_iff, mem_signKernel, pow_two]
  change (x.left.vector + permuteVector x.right.val x.left.vector = 0 ∧
    x.right * x.right = 1) ↔ _
  rw [hvec]
  exact and_comm

/-- Literal signed commutation in the left-action convention. The independent
signs cancel; the remaining equality includes the inversion correction. -/
theorem commute_iff_coordinates (x y : SplitExtension) :
    Commute x y ↔ x.right * y.right = y.right * x.right ∧
      x.left.vector + permuteVector x.right.val y.left.vector =
        y.left.vector + permuteVector y.right.val x.left.vector ∧
      signedCorrection x.right.val y.left.vector +
          cocycle x.left.vector.val (permuteVector x.right.val y.left.vector).val =
        signedCorrection y.right.val x.left.vector +
          cocycle y.left.vector.val (permuteVector y.right.val x.left.vector).val := by
  have hs : (x * y).left.sign = (y * x).left.sign ↔
      signedCorrection x.right.val y.left.vector +
          cocycle x.left.vector.val (permuteVector x.right.val y.left.vector).val =
        signedCorrection y.right.val x.left.vector +
          cocycle y.left.vector.val (permuteVector y.right.val x.left.vector).val := by
    change x.left.sign + (y.left.sign + signedCorrection x.right.val y.left.vector) +
        cocycle x.left.vector.val (permuteVector x.right.val y.left.vector).val =
      y.left.sign + (x.left.sign + signedCorrection y.right.val x.left.vector) +
        cocycle y.left.vector.val (permuteVector y.right.val x.left.vector).val ↔ _
    rw [show x.left.sign + (y.left.sign + signedCorrection x.right.val y.left.vector) +
        cocycle x.left.vector.val (permuteVector x.right.val y.left.vector).val =
      (x.left.sign + y.left.sign) + (signedCorrection x.right.val y.left.vector +
        cocycle x.left.vector.val (permuteVector x.right.val y.left.vector).val) by abel]
    rw [show y.left.sign + (x.left.sign + signedCorrection y.right.val x.left.vector) +
        cocycle y.left.vector.val (permuteVector y.right.val x.left.vector).val =
      (x.left.sign + y.left.sign) + (signedCorrection y.right.val x.left.vector +
        cocycle y.left.vector.val (permuteVector y.right.val x.left.vector).val) by abel]
    exact add_left_cancel_iff
  constructor
  · intro h
    exact ⟨congrArg SemidirectProduct.right h.eq,
      congrArg (fun z : SplitExtension => z.left.vector) h.eq,
      hs.mp (congrArg (fun z : SplitExtension => z.left.sign) h.eq)⟩
  · rintro ⟨hr, hv, hc⟩
    exact SemidirectProduct.ext (Model.ext (hs.mpr hc) hv) hr


/-- Square-admissible elements that commute with a specified element. -/
def squareCommutants (x : SplitExtension) : Set SplitExtension :=
  {y | y ^ 2 ∈ sign ∧ Commute x y}

/-- The finite commuting set in the literal signed coordinates. This is the
computational boundary for its cardinality estimate. -/
theorem mem_squareCommutants_iff_coordinates (x y : SplitExtension) :
    y ∈ squareCommutants x ↔
      (y.right ^ 2 = 1 ∧ permuteVector y.right.val y.left.vector = y.left.vector) ∧
      x.right * y.right = y.right * x.right ∧
      x.left.vector + permuteVector x.right.val y.left.vector =
        y.left.vector + permuteVector y.right.val x.left.vector ∧
      signedCorrection x.right.val y.left.vector +
          cocycle x.left.vector.val (permuteVector x.right.val y.left.vector).val =
        signedCorrection y.right.val x.left.vector +
          cocycle y.left.vector.val (permuteVector y.right.val x.left.vector).val := by
  change (y ^ 2 ∈ sign ∧ Commute x y) ↔ _
  rw [square_mem_sign_iff, commute_iff_coordinates]

/-- The same candidates, with commutation modulo sign with a second element.
The two displayed coordinate equalities are the literal quotient conventions. -/
def mixedCandidates (m : Model) (x : SplitExtension) : Set SplitExtension :=
  {y | y ^ 2 ∈ sign ∧ Commute (radicalEmbedding m) y ∧
    (x * y).right = (y * x).right ∧
    (x * y).left.vector = (y * x).left.vector}

/-- Any subgroup with the square bound, centralized by x, injects into its
square-admissible commuting candidates. -/
theorem card_le_squareCommutants (H : Subgroup SplitExtension)
    (hsq : ∀ y ∈ H, y ^ 2 ∈ sign) (x : SplitExtension)
    (hc : ∀ y ∈ H, Commute x y) :
    Nat.card H ≤ Nat.card (squareCommutants x) := by
  exact Nat.card_le_card_of_injective
    (fun y : H => (⟨y.val, hsq y.val y.property, hc y.val y.property⟩ : squareCommutants x))
    (fun _ _ h => Subtype.ext (congrArg (fun y : squareCommutants x => y.val) h))

/-- Commutation in the elementary actor image retains the literal right coordinates. -/
theorem mul_actors_commute (H : Subgroup SplitExtension)
    (hsq : ∀ y ∈ H, y ^ 2 ∈ sign)
    (x y : SplitExtension) (hx : x ∈ H) (hy : y ∈ H) :
    (x * y).right = (y * x).right := by
  have he := actorImage_elementary H hsq
  exact congrArg (fun a : actorImage H => a.val) (he.toIsMulCommutative.is_comm.comm
    (⟨x.right, x, hx, rfl⟩ : actorImage H)
    (⟨y.right, y, hy, rfl⟩ : actorImage H))

/-- The actual subgroup also injects into the mixed candidates whenever its
specified radical element is central. -/
theorem card_le_mixedCandidates (H : Subgroup SplitExtension)
    (hsq : ∀ y ∈ H, y ^ 2 ∈ sign) (m : Model) (x : SplitExtension)
    (hx : x ∈ H) (hc : ∀ y ∈ H, Commute (radicalEmbedding m) y) :
    Nat.card H ≤ Nat.card (mixedCandidates m x) := by
  exact Nat.card_le_card_of_injective
    (fun y : H => (⟨y.val, hsq y.val y.property, hc y.val y.property,
      mul_actors_commute H hsq x y.val hx y.property,
      mul_vectors_commute H hsq x y.val hx y.property⟩ : mixedCandidates m x))
    (fun _ _ h => Subtype.ext (congrArg (fun y : mixedCandidates m x => y.val) h))

/-- With trivial actor image, the order forces all of the embedded radical. -/
theorem eq_radical_of_actor_trivial (H : Subgroup SplitExtension)
    (hcard : Nat.card H = 64) (hact : ∀ x ∈ H, x.right = 1) :
    H = radicalEmbedding.range := by
  apply eq_of_le_of_card_ge
  · intro x hx
    exact ⟨x.left, SemidirectProduct.ext rfl (hact x hx).symm⟩
  · rw [Nat.card_congr (MonoidHom.ofInjective radicalEmbedding_injective).toEquiv.symm,
      EvenCliffordSix.card, hcard]

/-- This branch uses the already proved full center of the Clifford radical. -/
theorem center_eq_centralIn_of_actor_trivial (H : Subgroup SplitExtension)
    (hcard : Nat.card H = 64) (hact : ∀ x ∈ H, x.right = 1) :
    center H = centralIn H := by
  apply le_antisymm ?_ (centralIn_le_center H)
  intro z hz
  have he := eq_radical_of_actor_trivial H hcard hact
  have hm : z.val.left ∈ center Model := by
    apply mem_center_iff.mpr
    intro m
    have hmem : radicalEmbedding m ∈ H := by rw [he]; exact ⟨m, rfl⟩
    have h := congrArg (fun x : H => x.val.left)
      (mem_center_iff.mp hz ⟨radicalEmbedding m, hmem⟩)
    change m * action 1 z.val.left = z.val.left * action z.val.right m at h
    simpa only [hact z.val z.property, map_one, MulAut.one_apply] using h
  exact ⟨z.val.left, hm, SemidirectProduct.ext rfl (hact z.val z.property).symm⟩

end EvenCliffordSix.SplitExtension.ElementaryRestrictions
