module
public import Theory.SpecificGroups.GL2.ThreeResidualImages.Generation
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# The actual two-residual of GL₂(3) and its automorphisms

The upper and lower cubic unipotents generate the determinant kernel. Their
possible images under an automorphism are conjugate by an invertible matrix:
a kernel-checked calculation uses only the 81 two-by-two matrices. Consequently
GL₂(3) induces every automorphism of its two-residual SL₂(3). The centralizer
of that residual is precisely the scalar involution subgroup.

Source application: Aschbacher--Smith, Lemma 2.5.15, printed pp.558--559.
-/

public section
open Matrix Subgroup
namespace Matrix.GeneralLinearGroup
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)
@[expose] def threeLower : GL (Fin 2) (ZMod 3) :=
  mkOfDetNeZero !![(1 : ZMod 3),0;1,1] (by decide)
private theorem pair_match : ∀ B C : M, B ^ 3 = 1 → C ^ 3 = 1 →
    B ≠ 1 → C ≠ 1 → (B * C) ^ 4 = 1 → (B * C) ^ 2 ≠ 1 →
    ∃ A : M, A.det ≠ 0 ∧ A * threeUnipotent.val = B * A ∧
      A * threeLower.val = C * A := by
  decide +kernel

theorem three_twoResidual : pResidual 2 (GL (Fin 2) (ZMod 3)) = threeSpecialLinear := by
  apply le_antisymm (three_pPerfect_le_specialLinear _ (isPPerfect_pResidual 2))
  have hu3 : threeUnipotent ^ 3 = 1 := by decide +kernel
  have hl3 : threeLower ^ 3 = 1 := by decide +kernel
  have hu1 : threeUnipotent ≠ 1 := by decide +kernel
  have hl1 : threeLower ≠ 1 := by decide +kernel
  exact three_cubic_pair_generate _ threeUnipotent threeLower
    (mem_pResidual_of_orderOf_coprime (by rw [orderOf_eq_prime hu3 hu1]; decide))
    (mem_pResidual_of_orderOf_coprime (by rw [orderOf_eq_prime hl3 hl1]; decide))
    hu3 hl3 hu1 hl1 (by decide +kernel) (by decide +kernel)


private def upperS : threeSpecialLinear :=
  ⟨threeUnipotent, three_cubic_mem_specialLinear _ (by decide +kernel)⟩
private def lowerS : threeSpecialLinear :=
  ⟨threeLower, three_cubic_mem_specialLinear _ (by decide +kernel)⟩

private theorem hom_ext_pair {D : Type*} [Group D]
    (f g : threeSpecialLinear →* D) (hu : f upperS = g upperS)
    (hl : f lowerS = g lowerS) : f = g := by
  let J := f.eqLocus g
  have he : threeSpecialLinear ≤ J.map threeSpecialLinear.subtype := by
    exact three_cubic_pair_generate _ threeUnipotent threeLower
      (mem_map.mpr ⟨upperS, hu, rfl⟩) (mem_map.mpr ⟨lowerS, hl, rfl⟩)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  ext x
  obtain ⟨y, hy, hxy⟩ := he x.property
  have h : y = x := Subtype.ext hxy
  exact h ▸ hy

/-- Every automorphism of the actual determinant kernel is induced by GL₂(3). -/
theorem three_specialLinear_aut_surjective :
    Function.Surjective (MulAut.conjNormal : (GL (Fin 2) (ZMod 3)) →* MulAut threeSpecialLinear) := by
  intro a
  let B : M := (a upperS).val.val
  let C : M := (a lowerS).val.val
  have hB3 : B ^ 3 = 1 := by
    change ((a upperS) ^ 3).val.val = _
    rw [← map_pow, show upperS ^ 3 = 1 by decide +kernel, map_one]
    rfl
  have hC3 : C ^ 3 = 1 := by
    change ((a lowerS) ^ 3).val.val = _
    rw [← map_pow, show lowerS ^ 3 = 1 by decide +kernel, map_one]
    rfl
  have hB1 : B ≠ 1 := by
    intro h
    have h' : a upperS = a 1 := by rw [map_one]; exact Subtype.ext (Units.ext h)
    have hu : upperS ≠ 1 := by decide +kernel
    exact hu (a.injective h')
  have hC1 : C ≠ 1 := by
    intro h
    have h' : a lowerS = a 1 := by rw [map_one]; exact Subtype.ext (Units.ext h)
    have hl : lowerS ≠ 1 := by decide +kernel
    exact hl (a.injective h')
  have hBC4 : (B * C) ^ 4 = 1 := by
    change ((a upperS * a lowerS) ^ 4).val.val = _
    rw [← map_mul, ← map_pow, show (upperS * lowerS) ^ 4 = 1 by decide +kernel, map_one]
    rfl
  have hBC2 : (B * C) ^ 2 ≠ 1 := by
    intro h
    have h' : a ((upperS * lowerS) ^ 2) = a 1 := by
      rw [map_one, map_pow, map_mul]
      exact Subtype.ext (Units.ext h)
    have hn : (upperS * lowerS) ^ 2 ≠ 1 := by decide +kernel
    exact hn (a.injective h')
  obtain ⟨A, hA, hu, hl⟩ := pair_match B C hB3 hC3 hB1 hC1 hBC4 hBC2
  let g : GL (Fin 2) (ZMod 3) := mkOfDetNeZero A hA
  refine ⟨g, ?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext_pair
  · apply Subtype.ext
    change g * threeUnipotent * g⁻¹ = (a upperS).val
    apply mul_inv_eq_iff_eq_mul.mpr
    exact Units.ext hu
  · apply Subtype.ext
    change g * threeLower * g⁻¹ = (a lowerS).val
    apply mul_inv_eq_iff_eq_mul.mpr
    exact Units.ext hl

private theorem matrix_pair_centralizer : ∀ A : M, A.det ≠ 0 →
    A * threeUnipotent.val = threeUnipotent.val * A →
    A * threeLower.val = threeLower.val * A →
    A = 1 ∨ A = threeCentral.val := by decide +kernel

theorem three_specialLinear_centralizer :
    centralizer (threeSpecialLinear : Set (GL (Fin 2) (ZMod 3))) = zpowers threeCentral := by
  apply le_antisymm
  · intro x hx
    rcases matrix_pair_centralizer x.val x.det_ne_zero
      (congrArg Units.val (hx threeUnipotent upperS.property).symm)
      (congrArg Units.val (hx threeLower lowerS.property).symm) with h | h
    · have : x = 1 := Units.ext h
      simp [this]
    · exact Units.ext h ▸ mem_zpowers threeCentral
  · apply zpowers_le.mpr
    intro x hx
    apply Units.ext
    change x.val * threeCentral.val = threeCentral.val * x.val
    have h : ∀ A : M, A * threeCentral.val = threeCentral.val * A := by decide +kernel
    exact h x.val

/-- The scalar involution belongs to the determinant kernel. -/
theorem threeCentral_mem_specialLinear : threeCentral ∈ threeSpecialLinear := by
  exact (three_mem_specialLinear _).mpr (by decide +kernel)

/-- The marked scalar has order two. -/
theorem threeCentral_order : orderOf threeCentral = 2 := by
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

/-- The unique central involution of GL₂(3) is its marked scalar. -/
theorem three_central_involution_eq (z : GL (Fin 2) (ZMod 3))
    (hz : z ∈ center (GL (Fin 2) (ZMod 3))) (ho : orderOf z = 2) : z = threeCentral := by
  rcases matrix_pair_centralizer z.val z.det_ne_zero
    (congrArg Units.val (mem_center_iff.mp hz threeUnipotent).symm)
    (congrArg Units.val (mem_center_iff.mp hz threeLower).symm) with h | h
  · have he : z = 1 := Units.ext h
    simp [he] at ho
  · exact Units.ext h

end Matrix.GeneralLinearGroup
