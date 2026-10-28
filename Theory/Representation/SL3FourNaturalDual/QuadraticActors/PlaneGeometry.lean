module

public import Theory.Representation.SL3FourNaturalDual

/-!
# Full field lines in binary subspaces of the F₄-plane

For a binary subspace D of dimension at least three, the map from D to the
quotient by D given by multiplication by omega has nonzero kernel. A vector
in that kernel, together with its omega multiple, supplies a full F₄-line.
Dimension then supplies an independent parameter, and the resulting basis
puts the line and that parameter on the two coordinate axes simultaneously.

This is the parameter-space geometry needed for the root-plane alternative
in Aschbacher--Smith, proof of 13.8.20, printed p.955 (1 March 2004 manuscript).
-/

@[expose] public section
open Representation
namespace Representation.SL3FourNaturalDual.QuadraticActors

lemma field_four_cases (a : F) : a = 0 ∨ a = 1 ∨ a = omega ∨ a = 1 + omega := by
  revert a
  decide +kernel

lemma all_scalars_mem {X : Type*} [AddCommGroup X] [Module F X]
    [Module (ZMod 2) X] (D : Submodule (ZMod 2) X) (x : X)
    (hx : x ∈ D) (hw : omega • x ∈ D) : ∀ a : F, a • x ∈ D := by
  intro a
  rcases field_four_cases a with rfl | rfl | rfl | rfl
  · simp
  · simpa using hx
  · exact hw
  · simpa only [add_smul, one_smul] using D.add_mem hx hw

/-- Every binary subspace of the F₄-plane of dimension at least three
contains a full F₄-line. -/
theorem exists_full_line (D : Submodule (ZMod 2) (F × F))
    (hD : 3 ≤ Module.finrank (ZMod 2) D) :
    ∃ x : F × F, x ≠ 0 ∧ ∀ a : F, a • x ∈ D := by
  let f : D →ₗ[ZMod 2] ((F × F) ⧸ D) :=
    D.mkQ.comp (((LinearMap.lsmul F (F × F) omega).restrictScalars (ZMod 2)).comp D.subtype)
  have hdim : Module.finrank (ZMod 2) (F × F) = 4 := by
    rw [Module.finrank_prod, finrank_field]
  have hquot := D.finrank_quotient_add_finrank
  have hrange := f.range.finrank_le
  have hker := f.finrank_range_add_finrank_ker
  have hpos : 0 < Module.finrank (ZMod 2) f.ker := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hn : (x.val.val : F × F) ≠ 0 := by
    intro h
    exact hx (Subtype.ext (Subtype.ext h))
  refine ⟨x.val.val, hn, all_scalars_mem D _ x.val.property ?_⟩
  have hk := x.property
  change D.mkQ (omega • x.val.val) = 0 at hk
  exact (Submodule.Quotient.mk_eq_zero D).mp hk

/-- A three-dimensional binary subspace contains a full root line together
with an element outside that F₄-line. -/
theorem exists_full_line_and_independent (D : Submodule (ZMod 2) (F × F))
    (hD : 3 ≤ Module.finrank (ZMod 2) D) :
    ∃ x y : F × F, x ≠ 0 ∧ (∀ a : F, a • x ∈ D) ∧
      y ∈ D ∧ y ∉ Submodule.span F {x} := by
  obtain ⟨x, hx, hline⟩ := exists_full_line D hD
  suffices ∃ y, y ∈ D ∧ y ∉ Submodule.span F {x} by
    obtain ⟨y, hy, hn⟩ := this
    exact ⟨x, y, hx, hline, hy, hn⟩
  by_contra! h
  have hle : D ≤ (Submodule.span F {x}).restrictScalars (ZMod 2) := by
    intro y hy
    exact h y hy
  have hdim : Module.finrank (ZMod 2)
      ((Submodule.span F {x}).restrictScalars (ZMod 2)) = 2 := by
    let e := LinearEquiv.toSpanNonzeroSingleton F (F × F) x hx
    exact ((e.restrictScalars (ZMod 2)).finrank_eq.symm).trans finrank_field
  have hh := Submodule.finrank_mono hle
  omega

/-- Simultaneous coordinates for a full root direction and an independent
root parameter. No determinant-one restriction is imposed on this change
of coordinates. -/
theorem coordinates_of_independent (x y : F × F) (hx : x ≠ 0)
    (hy : y ∉ Submodule.span F {x}) :
    ∃ e : (F × F) ≃ₗ[F] (F × F), e x = (0, 1) ∧ e y = (1, 0) := by
  have hi : LinearIndependent F ![x, y] := (LinearIndependent.pair_iff' hx).mpr (by
    intro a ha
    exact hy (Submodule.mem_span_singleton.mpr ⟨a, ha⟩))
  have hj : LinearIndependent F ![y, x] := LinearIndependent.pair_symm_iff.mpr hi
  have hd : Fintype.card (Fin 2) = Module.finrank F (F × F) := by
    simp [Module.finrank_prod]
  let b := basisOfLinearIndependentOfCardEqFinrank hj hd
  have hb0 : b 0 = y := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  let e := b.equivFun.trans (LinearEquiv.finTwoArrow F F)
  refine ⟨e, ?_, ?_⟩
  · rw [← hb1]
    change (b.equivFun (b 1) 0, b.equivFun (b 1) 1) = (0, 1)
    simp
  · rw [← hb0]
    change (b.equivFun (b 0) 0, b.equivFun (b 0) 1) = (1, 0)
    simp

/-- A binary subspace of dimension at least three can be put in coordinates
containing the full second axis and the first unit vector simultaneously. -/
theorem exists_plane_coordinates (D : Submodule (ZMod 2) (F × F))
    (hD : 3 ≤ Module.finrank (ZMod 2) D) :
    ∃ e : (F × F) ≃ₗ[F] (F × F),
      (∀ a : F, e.symm (0, a) ∈ D) ∧ e.symm (1, 0) ∈ D := by
  obtain ⟨x, y, hx, hline, hy, hyx⟩ := exists_full_line_and_independent D hD
  obtain ⟨e, hex, hey⟩ := coordinates_of_independent x y hx hyx
  refine ⟨e, ?_, ?_⟩
  · intro a
    have he : e (a • x) = (0, a) := by rw [map_smul, hex]; simp
    rw [← he, e.symm_apply_apply]
    exact hline a
  · rw [← hey, e.symm_apply_apply]
    exact hy

end Representation.SL3FourNaturalDual.QuadraticActors
