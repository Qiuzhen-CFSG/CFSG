module

public import Theory.Representation.BinaryPermutationNaturalStructure
public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# The split extension of the six-letter augmentation core

This is the actual semidirect product of the even-weight binary six-space by
A6, with the coordinate-permutation convention of BinaryPermutation. Its
constant line is defined through the literal natural-module projection.
A displayed element squares to the weight-four complement of a weight-two
vector. Fixing its first coordinate rules out the other lift in that coset.

The final conditional calculation isolates two outstanding residual facts; it
does not assert either residual or core identity. Those identities are needed
before applying this model to the source theorem.

Source: Aschbacher–Smith, I.2.2(6b), printed pp.410 and 412, combined
manuscript of 1 March 2004.
-/

@[expose] public section

namespace BinaryPermutation.SixCoreExtension
open Subgroup
noncomputable section
abbrev V := core (Fin 6)
abbrev A := alternatingGroup (Fin 6)
noncomputable def action : A →* MulAut (Multiplicative V) where
  toFun g := (LinearEquiv.ofBijective (coreRepresentation (Fin 6) g.val)
    ((coreRepresentation (Fin 6)).apply_bijective g.val)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (coreRepresentation (Fin 6) 1 v.toAdd) = v
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (coreRepresentation (Fin 6) (g.val * h.val) v.toAdd) =
      Multiplicative.ofAdd (coreRepresentation (Fin 6) g.val
        (coreRepresentation (Fin 6) h.val v.toAdd))
    rw [map_mul, Module.End.mul_apply]
abbrev Model := Multiplicative V ⋊[action] A

def vector : Multiplicative V →* Model := SemidirectProduct.inl

def constant : V := ⟨![1, 1, 1, 1, 1, 1], by rw [mem_core]; decide⟩
def pair : V := ⟨![1, 1, 0, 0, 0, 0], by rw [mem_core]; decide⟩
def four : V := ⟨![0, 0, 1, 1, 1, 1], by rw [mem_core]; decide⟩
def root : Model :=
  ⟨Multiplicative.ofAdd ⟨![0, 0, 1, 0, 1, 0], by rw [mem_core]; decide⟩,
    ⟨Equiv.swap 2 3 * Equiv.swap 4 5, by simp [Equiv.Perm.mem_alternatingGroup]⟩⟩

theorem pair_add_constant : pair + constant = four := by decide

theorem square_left (x : Model) (i : Fin 6) :
    (x ^ 2).left.toAdd.val i =
      x.left.toAdd.val i + x.left.toAdd.val (x.right.val.symm i) := by
  rw [pow_two]
  rfl

theorem root_sq : root ^ 2 = vector (Multiplicative.ofAdd four) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · apply Subtype.ext
    ext i
    fin_cases i <;> rfl

/-- The marked central line in the extension. -/
def centralLine : Subgroup Model :=
  (AddSubgroup.toSubgroup ((coreToNatural (Fin 6)).ker.toAddSubgroup)).map vector

/-- Equality of cosets of the constant line on two vectors. -/
theorem vector_fiber (v w : V) :
    (vector (Multiplicative.ofAdd v))⁻¹ * vector (Multiplicative.ofAdd w) ∈ centralLine ↔
      coreToNatural (Fin 6) v = coreToNatural (Fin 6) w := by
  rw [← map_inv, ← map_mul]
  change vector (Multiplicative.ofAdd (-v + w)) ∈ centralLine ↔ _
  change Multiplicative.ofAdd (-v + w) ∈
    (centralLine.comap vector) ↔ _
  rw [centralLine, comap_map_eq_self_of_injective (show Function.Injective vector from
    SemidirectProduct.inl_injective)]
  change coreToNatural (Fin 6) (-v + w) = 0 ↔ _
  rw [map_add, map_neg, neg_add_eq_zero]

/-- A square whose actor fixes the first coordinate cannot be the weight-two
representative of this constant-line coset. -/
theorem square_fiber_eq_four (x : Model) (v : V)
    (hfix : x.right.val 0 = 0)
    (hsq : x ^ 2 = vector (Multiplicative.ofAdd v))
    (hfib : coreToNatural (Fin 6) v = coreToNatural (Fin 6) pair) : v = four := by
  have hz : v.val 0 = 0 := by
    have h0 := congrArg (fun y : Model => y.left.toAdd.val 0) hsq
    rw [square_left] at h0
    have hi : x.right.val.symm 0 = 0 := by
      apply x.right.val.injective
      rw [Equiv.apply_symm_apply, hfix]
    rw [hi, CharTwo.add_self_eq_zero] at h0
    exact h0.symm
  have hd : v.val - pair.val ∈ constants (Fin 6) := by
    exact (Submodule.Quotient.eq _).mp (congrArg Subtype.val hfib)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd
  have hc1 : c = 1 := by
    have h0 := congrFun hc 0
    simpa [allOne, pair, hz] using h0
  subst c
  apply Subtype.ext
  have h : v.val = pair.val + allOne (Fin 6) := by
    simpa only [one_smul, sub_eq_iff_eq_add, add_comm] using hc.symm
  rw [h]
  funext i
  fin_cases i <;> rfl
theorem four_natural_eq_pair :
    coreToNatural (Fin 6) four = coreToNatural (Fin 6) pair := by
  apply Subtype.ext
  apply (Submodule.Quotient.eq _).mpr
  have he : four.val - pair.val = allOne (Fin 6) := by
    funext i
    fin_cases i <;> rfl
  change four.val - pair.val ∈ constants (Fin 6)
  rw [he]
  exact Submodule.subset_span (Set.mem_singleton _)

/-- The square calculation reduces the source clause to two residual facts:
the residual fixes the first point, and its two-core contains the displayed root.
The residual and core identities establishing these facts are separate obligations. -/
theorem unique_square_fiber_pair
    (hfix : ∀ x ∈ Theory.GroupTheory.centralizerResidualCore (vector (Multiplicative.ofAdd pair)),
      x.right.val 0 = 0)
    (hroot : root ∈ Theory.GroupTheory.centralizerResidualCore (vector (Multiplicative.ofAdd pair))) :
    ∃! v : Model,
      (vector (Multiplicative.ofAdd pair))⁻¹ * v ∈ centralLine ∧
      ∃ x ∈ Theory.GroupTheory.centralizerResidualCore (vector (Multiplicative.ofAdd pair)),
        x ^ 2 = v := by
  refine ⟨vector (Multiplicative.ofAdd four),
    ⟨(vector_fiber pair four).mpr four_natural_eq_pair.symm, root, hroot, root_sq⟩, ?_⟩
  rintro v ⟨hv, x, hx, hsq⟩
  have hvRange : v ∈ vector.range := by
    have hc : (vector (Multiplicative.ofAdd pair))⁻¹ * v ∈ vector.range :=
      Subgroup.map_le_range _ _ hv
    simpa only [mul_inv_cancel_left] using
      vector.range.mul_mem (show vector (Multiplicative.ofAdd pair) ∈ vector.range from
        ⟨Multiplicative.ofAdd pair, rfl⟩) hc
  obtain ⟨w, rfl⟩ := hvRange
  have hw := square_fiber_eq_four x w.toAdd (hfix x hx) hsq
    ((vector_fiber pair w.toAdd).mp hv).symm
  exact congrArg (fun z : V => vector (Multiplicative.ofAdd z)) hw
end
end BinaryPermutation.SixCoreExtension
