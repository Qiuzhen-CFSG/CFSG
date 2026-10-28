module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.LocalActions
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.GroupTheory.LocalNormalizerUniqueness
import Mathlib.Tactic.FinCases

/-!
# Full parabolic actions on the symplectic local quotients

The local two-cores have the standard point and plane as their common fixed
spaces. Their proved normalizers therefore identify the local normalizers.
The middle block on the point parabolic and the upper-left block on the plane
parabolic give the actual quotient conjugation formulas, retaining every
scalar in the parabolic torus.

Source: the local kernel calculation used in Aschbacher--Smith F.1.12,
printed p.264 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F]

private theorem pointParabolic_row_zero (g : pointParabolic (F := F))
    (j : Fin 2 ⊕ Fin 2) (hj : j ≠ .inr 0) : g.val.val (.inr 0) j = 0 := by
  have h := preserves_form g.val (e (F := F) 0) (Pi.single j 1)
  rw [pointParabolic_smul_e_zero g] at h
  have ha : g.val.val (.inl 0) (.inl 0) ≠ 0 := by
    rw [← determinantCharacter_point_coe g]
    exact Units.ne_zero _
  simpa [map_smul, form_apply, e, Fin.sum_univ_two, smul_eq_mulVec,
    Matrix.mulVec_single, Pi.single_apply, Ne.symm hj, ha] using h

/-- The action on the perpendicular space modulo the point, for the full parabolic. -/
def pointParabolicQuotient : pointParabolic (F := F) →*
    Matrix.SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨g.val.val.submatrix middleIndex middleIndex, by
    have h := preserves_form g.val (e (F := F) 1) (Pi.single (.inr 1) 1)
    simpa [middleIndex, Matrix.det_fin_two, Matrix.submatrix,
      form_apply, smul_eq_mulVec, e, Matrix.mulVec_single, Fin.sum_univ_two,
      pointParabolic_row_zero g (.inl 1) (by decide),
      pointParabolic_row_zero g (.inr 1) (by decide), mul_comm] using h⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    apply Subtype.ext
    ext i j
    change (g.val.val * h.val.val) (middleIndex i) (middleIndex j) =
      (g.val.val.submatrix middleIndex middleIndex *
        h.val.val.submatrix middleIndex middleIndex) i j
    have hc := (mem_pointParabolic_iff g.val).mp g.property
    fin_cases i <;> fin_cases j <;>
      simp [middleIndex, Matrix.mul_apply, Matrix.submatrix,
        Fintype.sum_sum_type, Fin.sum_univ_two, hc.1, hc.2,
        pointParabolic_row_zero h (.inl 1) (by decide),
        pointParabolic_row_zero h (.inr 1) (by decide)]

@[simp] theorem pointParabolicQuotient_local (l : pointLocal (F := F)) :
    pointParabolicQuotient ⟨l.val, pointLocal_le l.property⟩ = pointQuotient l := rfl

/-- Full parabolic conjugation on the point quotient. -/
theorem pointQuotient_conjugate (g : pointParabolic (F := F))
    (l : pointLocal (F := F))
    (hl : g.val * l.val * g.val⁻¹ ∈ pointLocal) :
    pointQuotient ⟨g.val * l.val * g.val⁻¹, hl⟩ =
      pointParabolicQuotient g * pointQuotient l * (pointParabolicQuotient g)⁻¹ := by
  change pointParabolicQuotient
    (g * ⟨l.val, pointLocal_le l.property⟩ * g⁻¹) = _
  simp

/-- Full parabolic conjugation on the plane quotient, with its GL₂ scalar contribution. -/
theorem planeQuotient_conjugate (g : planeParabolic (F := F))
    (l : planeLocal (F := F))
    (hl : g.val * l.val * g.val⁻¹ ∈ planeLocal) :
    (Plane.quotientMap ⟨g.val * l.val * g.val⁻¹, hl⟩).val =
      Plane.upperLeft g * (Plane.quotientMap l).val * Plane.upperLeft g⁻¹ := by
  change Plane.upperLeft (g * ⟨l.val, planeLocal_le l.property⟩ * g⁻¹) = _
  rw [map_mul, map_mul]
  rfl

/-- The point quotient retains the second torus coordinate. -/
theorem pointParabolicQuotient_torus (a b : Fˣ) :
    (pointParabolicQuotient
      ⟨diagonalTorus a b, (diagonalTorus_mem_borel a b).1⟩).val =
      Matrix.diagonal ![(b : F), (↑b⁻¹ : F)] := by
  ext i j
  change (diagonalTorus a b).val (middleIndex i) (middleIndex j) = _
  fin_cases i <;> fin_cases j <;> simp [diagonalTorus, middleIndex, Matrix.diagonal]

/-- The plane quotient retains both torus coordinates before conjugation. -/
theorem planeUpperLeft_torus (a b : Fˣ) :
    Plane.upperLeft ⟨diagonalTorus a b, (diagonalTorus_mem_borel a b).2⟩ =
      Matrix.diagonal ![(a : F), (b : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Plane.upperLeft, diagonalTorus,
    Matrix.toBlocks₁₁, Matrix.diagonal]

variable [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

include hcard hn in
/-- The normalizer of the actual point-local factor is the full point parabolic. -/
theorem pointLocal_normalizer :
    Subgroup.normalizer (pointLocal (F := F) : Set (Sp F)) = pointParabolic := by
  apply le_antisymm
  · intro g hg
    have hc := Subgroup.normalizer_le_normalizer_characteristic_image
      (pointLocal (F := F)) (pCore 2 pointLocal) hg
    rw [pointLocal_core_eq hcard hn] at hc
    exact (pointRadicalAmbient_normalizer hcard hn) ▸ hc
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer pointLocal_le).mp inferInstance

include hcard hn in
/-- The normalizer of the actual plane-local factor is the full plane parabolic. -/
theorem planeLocal_normalizer :
    Subgroup.normalizer (planeLocal (F := F) : Set (Sp F)) = planeParabolic := by
  apply le_antisymm
  · intro g hg
    have hc := Subgroup.normalizer_le_normalizer_characteristic_image
      (planeLocal (F := F)) (pCore 2 planeLocal) hg
    rw [planeLocal_core_eq hcard hn] at hc
    exact (planeRadicalAmbient_normalizer hcard hn) ▸ hc
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer planeLocal_le).mp inferInstance

omit [Finite F] [CharP F 2] in
private theorem inner_map_of_mul_map (L : Subgroup (Sp F)) (a b : MulAut (Sp F))
    (hab : L.map (a * b).toMonoidHom = L) (hb : L.map b.toMonoidHom = L) :
    L.map a.toMonoidHom = L := by
  calc
    _ = (L.map b.toMonoidHom).map a.toMonoidHom := by rw [hb]
    _ = L := by rw [Subgroup.map_map]; exact hab

include hcard hn in
/-- A semilinear automorphism fixing the point factor has its linear part in its parabolic. -/
theorem point_semilinear_mem_parabolic (g : Sp F) (σ : F ≃+* F)
    (hL : pointLocal.map ((MulAut.conj g) * fieldAutomorphism σ).toMonoidHom = pointLocal) :
    g ∈ pointParabolic := by
  rw [← pointLocal_normalizer hcard hn, Subgroup.mem_normalizer_iff_map_conj_eq]
  exact inner_map_of_mul_map _ _ _ hL
    (pointLocal_map hcard hn _ (field_map_pointParabolic σ))

include hcard hn in
/-- A semilinear automorphism fixing the plane factor has its linear part in its parabolic. -/
theorem plane_semilinear_mem_parabolic (g : Sp F) (σ : F ≃+* F)
    (hL : planeLocal.map ((MulAut.conj g) * fieldAutomorphism σ).toMonoidHom = planeLocal) :
    g ∈ planeParabolic := by
  rw [← planeLocal_normalizer hcard hn, Subgroup.mem_normalizer_iff_map_conj_eq]
  exact inner_map_of_mul_map _ _ _ hL
    (planeLocal_map hcard hn _ (field_map_planeParabolic σ))

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
