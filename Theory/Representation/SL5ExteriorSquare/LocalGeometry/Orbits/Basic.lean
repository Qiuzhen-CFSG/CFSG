module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Involutions
import Mathlib.Tactic.FinCases

/-!
# Orbits and point stabilizers in the binary exterior square

We use the literal action of SL₅(2) on Λ²(F₂⁵). Over F₂ each projective point
has a unique nonzero vector, so its setwise stabilizer is the vector stabilizer.
The shared last-column shears fix the second source representative: each factor
fixes the first four natural basis vectors, and hence both of its wedge terms.
This supplies the inclusion of the proposed kernel in the actual stabilizer;
normality and the quotient identification require separate proofs.

Source: Aschbacher–Smith, 12.5.5(2–3), printed p.819/PDF p.836.
-/

@[expose] public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- The orbit relation for the genuine exterior action. -/
def InExteriorOrbit (v w : V) : Prop := ∃ g : Group, exteriorAction 2 g v = w

/-- The subgroup fixing an exterior vector. -/
noncomputable def vectorStabilizer (v : V) : Subgroup Group where
  carrier := {g | exteriorAction 2 g v = v}
  one_mem' := by change exteriorAction 2 1 v = v; rw [map_one]; rfl
  mul_mem' := by
    intro g h hg hh
    change exteriorAction 2 (g * h) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change exteriorAction 2 g⁻¹ v = v
    have h := congrArg (exteriorAction 2 g⁻¹) hg
    change (exteriorAction 2 g⁻¹ * exteriorAction 2 g) v = exteriorAction 2 g⁻¹ v at h
    rw [← map_mul, inv_mul_cancel, map_one] at h
    exact h.symm

@[simp] theorem mem_vectorStabilizer (v : V) (g : Group) :
    g ∈ vectorStabilizer v ↔ exteriorAction 2 g v = v := Iff.rfl

/-- The source's second point V₁₀′. -/
noncomputable def nondecomposablePoint : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {nondecomposable}

/-- The literal stabilizer whose quotient is to be identified with S₆. -/
noncomputable abbrev nondecomposableStabilizer : Subgroup Group :=
  vectorStabilizer nondecomposable

@[simp] theorem coordinates_basis (i : Fin 10) : coordinates (basis i) = Pi.single i 1 := by
  ext j
  change basis.equivFun (basis i) j = (Pi.single i 1 : Coordinates) j
  simp only [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]

theorem coordinates_decomposable :
    coordinates decomposable = ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [decomposable, coordinates_basis]
  ext i
  fin_cases i <;> rfl

theorem coordinates_nondecomposable :
    coordinates nondecomposable = ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0] := by
  rw [nondecomposable, map_add, coordinates_basis, coordinates_basis]
  ext i
  fin_cases i <;> rfl

theorem decomposable_ne_zero : decomposable ≠ 0 := by
  intro h
  have he := congrArg (fun v => coordinates v 0) h
  rw [coordinates_decomposable, map_zero] at he
  exact one_ne_zero he

theorem nondecomposable_ne_zero : nondecomposable ≠ 0 := by
  intro h
  have he := congrArg (fun v => coordinates v 0) h
  rw [coordinates_nondecomposable, map_zero] at he
  exact one_ne_zero he

theorem decomposable_ne_nondecomposable : decomposable ≠ nondecomposable := by
  intro h
  have he := congrArg (fun v => coordinates v 7) h
  rw [coordinates_decomposable, coordinates_nondecomposable] at he
  change (0 : ZMod 2) = 1 at he
  exact zero_ne_one he

theorem InExteriorOrbit.refl (v : V) : InExteriorOrbit v v := by
  refine ⟨1, ?_⟩
  rw [map_one]
  rfl

theorem InExteriorOrbit.symm {v w : V} (h : InExteriorOrbit v w) : InExteriorOrbit w v := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  change (exteriorAction 2 g⁻¹ * exteriorAction 2 g) v = v
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

theorem InExteriorOrbit.trans {u v w : V} (h : InExteriorOrbit u v)
    (h' : InExteriorOrbit v w) : InExteriorOrbit u w := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨g', rfl⟩ := h'
  exact ⟨g' * g, by rw [map_mul]; rfl⟩

private theorem exteriorAction_injective (g : Group) : Function.Injective (exteriorAction 2 g) := by
  intro v w h
  have he := congrArg (exteriorAction 2 g⁻¹) h
  change (exteriorAction 2 g⁻¹ * exteriorAction 2 g) v =
    (exteriorAction 2 g⁻¹ * exteriorAction 2 g) w at he
  rwa [← map_mul, inv_mul_cancel, map_one] at he

theorem InExteriorOrbit.eq_zero_iff {v w : V} (h : InExteriorOrbit v w) : v = 0 ↔ w = 0 := by
  obtain ⟨g, rfl⟩ := h
  exact ((exteriorAction_injective g).eq_iff' (map_zero (exteriorAction 2 g))).symm

/-- Binary projective points have a unique nonzero vector. -/
theorem mem_binaryPoint (v w : V) :
    w ∈ Submodule.span (ZMod 2) {v} ↔ w = 0 ∨ w = v := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    have hc : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    rcases hc with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

/-- Fixing a binary vector is equivalent to stabilizing its projective point. -/
theorem vectorStabilizer_eq_exteriorStabilizer_point (v : V) :
    vectorStabilizer v = exteriorStabilizer (Submodule.span (ZMod 2) {v}) := by
  ext g
  change exteriorAction 2 g v = v ↔ ∀ w, exteriorAction 2 g w ∈
    Submodule.span (ZMod 2) {v} ↔ w ∈ Submodule.span (ZMod 2) {v}
  simp only [mem_binaryPoint]
  constructor
  · intro hg w
    constructor
    · rintro (h | h)
      · exact Or.inl ((exteriorAction_injective g) (h.trans (map_zero _).symm))
      · exact Or.inr ((exteriorAction_injective g) (h.trans hg.symm))
    · rintro (rfl | rfl)
      · exact Or.inl (map_zero _)
      · exact Or.inr hg
  · intro h
    rcases (h v).mpr (Or.inr rfl) with hz | he
    · have hv : v = 0 := (exteriorAction_injective g) (hz.trans (map_zero _).symm)
      rw [hv, map_zero]
    · exact he

/-- The vector-stabilizer convention agrees with the source centralizer of V₁₀′. -/
theorem nondecomposableStabilizer_eq_pointStabilizer :
    nondecomposableStabilizer = exteriorStabilizer nondecomposablePoint :=
  vectorStabilizer_eq_exteriorStabilizer_point _

private theorem shear_fixes_standard (u : Fin 4 → ZMod 2) (j : Fin 4) :
    (shear u).val.mulVec (Pi.single j.castSucc 1) = Pi.single j.castSucc 1 := by
  change specialLinearNatural 5 (shear u) _ = _
  unfold shear
  apply List.prod_induction (fun g : Group =>
    specialLinearNatural 5 g (Pi.single j.castSucc 1) = Pi.single j.castSucc 1)
  · intro a b ha hb
    rw [map_mul, Module.End.mul_apply, hb, ha]
  · rw [map_one]
    rfl
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    change (Matrix.SpecialLinearGroup.transvection (i := i.castSucc)
      (j := (4 : Fin 5)) _ (u i)).val.mulVec _ = _
    rw [Matrix.SpecialLinearGroup.transvection_coe]
    have hj : (4 : Fin 5) ≠ j.castSucc := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc] at this
      omega
    simp [-Matrix.mulVec_single, Matrix.add_mulVec, Matrix.single_mulVec_eq, hj]

/-- The specified last-column shears fix e₁∧e₂ + e₃∧e₄. -/
theorem shear_fixes_nondecomposable (u : Fin 4 → ZMod 2) :
    exteriorAction 2 (shear u) nondecomposable = nondecomposable := by
  rw [nondecomposable, map_add]
  have h (s : Fin 10) (hs : s = 0 ∨ s = 7) :
      exteriorAction 2 (shear u) (basis s) = basis s := by
    rw [basis_wedge, exteriorAction_ιMulti]
    congr 1
    funext i
    rcases hs with rfl | rfl
    · fin_cases i
      · exact shear_fixes_standard u 0
      · exact shear_fixes_standard u 1
    · fin_cases i
      · exact shear_fixes_standard u 2
      · exact shear_fixes_standard u 3
  rw [h 0 (Or.inl rfl), h 7 (Or.inr rfl)]

/-- The shared shear subgroup embeds in the literal stabilizer. -/
theorem shearSubgroup_le_nondecomposableStabilizer :
    shearSubgroup ≤ nondecomposableStabilizer := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, rfl⟩
  exact shear_fixes_nondecomposable u

end Representation.SL5ExteriorSquare
