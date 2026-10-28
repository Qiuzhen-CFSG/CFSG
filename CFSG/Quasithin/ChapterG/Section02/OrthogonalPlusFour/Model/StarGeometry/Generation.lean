module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model.StarGeometry.Points

/-!
# Generation by the original two conjugate point stabilizers

Conjugation uses the original g, with the source convention Uᵍ = g⁻¹Ug.
Equivariance transports that same conjugation through the given matrix
projection. The source perpendicular-hyperplane condition supplies two
nonorthogonal marked vectors. The finite determinant calculation generates
the whole model, and injectivity of the supplied equivalence returns equality
of the literal starred subgroups. The residual lift remains in Model.Maps.
Source: Aschbacher–Smith, G.2.6, printed p.336, first proof paragraph.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup ClassicalOrthogonal.FourPlusMatrix
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- The actual image of g⁻¹, not a replacement conjugator. -/
def rightConjugatingPair : PairSL (F := ZMod 2) :=
  d.matrixProjection ⟨g⁻¹, mem_sup_left (D.L.inv_mem d.g_mem)⟩

/-- Coordinates of the original right conjugate of a marked vector. -/
def conjugatePointVector (z : D.V₁) : Mat (F := ZMod 2) :=
  matrixAction d.rightConjugatingPair (d.pointVector z)

theorem conjugatePointVector_ambient (z : D.V₁) :
    (d.coordinates.symm (Multiplicative.ofAdd (d.conjugatePointVector z)) : G) =
      g⁻¹ * (z : G) * g := by
  simpa [conjugatePointVector, rightConjugatingPair, pointVector, matrixProjection] using
    d.equivariant ⟨g⁻¹, mem_sup_left (D.L.inv_mem d.g_mem)⟩
      (inclusion (point_le_VL D) z)

/-- The source noncontainment is a nonzero pairing on the actual two points. -/
theorem exists_nonorthogonal_pointVectors :
    ∃ z w : D.V₁, (determinantForm (F := ZMod 2)).polarBilin
      (d.conjugatePointVector z) (d.pointVector w) ≠ 0 := by
  by_contra! hn
  apply d.nonorthogonal
  rintro _ ⟨z, hz, rfl⟩
  let v : D.VL := d.coordinates.symm (Multiplicative.ofAdd (d.conjugatePointVector ⟨z, hz⟩))
  have hv : (v : G) ∈ D.V := (d.perpendicular v).mpr (by
    intro w
    have hw : inclusion (point_le_VL D) w = (⟨w, point_le_VL D w.property⟩ : D.VL) :=
      Subtype.ext rfl
    simpa only [v, MulEquiv.apply_symm_apply, toAdd_ofAdd, pointVector, hw] using hn ⟨z, hz⟩ w)
  change g⁻¹ * z * (g⁻¹)⁻¹ ∈ D.V
  simpa only [v, d.conjugatePointVector_ambient, inv_inv] using hv

/-- The literal conjugate image, through the same LU projection. -/
theorem modelImage_conjugate_U :
    d.modelImage (conjugate D.U g) =
      (d.modelImage D.U).map (MulAut.conj d.rightConjugatingPair).toMonoidHom := by
  let t : (D.L ⊔ D.U : Subgroup G) := ⟨g⁻¹, mem_sup_left (D.L.inv_mem d.g_mem)⟩
  have he (u : (D.L ⊔ D.U : Subgroup G)) :
      d.matrixProjection (t * u * t⁻¹) =
        MulAut.conj d.rightConjugatingPair (d.matrixProjection u) := by
    simp only [map_mul, map_inv, MulAut.conj_apply]
    rfl
  ext b
  constructor
  · rintro ⟨u, ⟨v, hv, hvu⟩, rfl⟩
    let v' : (D.L ⊔ D.U : Subgroup G) := ⟨v, mem_sup_right hv⟩
    have hu : t * v' * t⁻¹ = u := by
      apply Subtype.ext
      change g⁻¹ * v * (g⁻¹)⁻¹ = (u : G) at hvu ⊢
      exact hvu
    exact ⟨d.matrixProjection v', ⟨v', hv, rfl⟩, (he v').symm.trans (congrArg _ hu)⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨t * u * t⁻¹, ?_, he u⟩
    exact ⟨u, hu, rfl⟩

/-- The two source-marked images generate the actual determinant model. -/
theorem modelImage_I_eq_top : d.modelImage (D.I g) = ⊤ := by
  obtain ⟨z, w, hzw⟩ := d.exists_nonorthogonal_pointVectors
  have hz : d.pointVector z ≠ 0 := by
    intro hz
    apply hzw
    simp [conjugatePointVector, hz]
  have hw : d.pointVector w ≠ 0 := by
    intro hw
    apply hzw
    simp [hw]
  have hgen := PrimeFieldTwo.singular_stabilizers_generate
    (d.conjugatePointVector z) (d.pointVector w)
    (by rw [conjugatePointVector, matrixAction_det];
        exact (determinantForm_apply _).symm.trans (d.pointVector_singular z))
    ((determinantForm_apply _).symm.trans (d.pointVector_singular w)) hzw
  have hconj : conjugate D.U g ≤ D.L ⊔ D.U := le_sup_right.trans d.I_le_LU
  change ((D.U ⊔ conjugate D.U g).subgroupOf (D.L ⊔ D.U)).map d.matrixProjection = ⊤
  rw [subgroupOf_sup le_sup_right hconj, Subgroup.map_sup]
  change d.modelImage D.U ⊔ d.modelImage (conjugate D.U g) = ⊤
  rw [d.modelImage_conjugate_U, d.modelImage_U_eq_vector_stabilizer z hz,
    ← PrimeFieldTwo.stabilizer_action]
  have he : PrimeFieldTwo.stabilizer (d.pointVector z) =
      PrimeFieldTwo.stabilizer (d.pointVector w) :=
    (d.modelImage_U_eq_vector_stabilizer z hz).symm.trans
      (d.modelImage_U_eq_vector_stabilizer w hw)
  rw [he, sup_comm]
  exact hgen

/-- Starred generation for the original quotient map and original g. -/
theorem star_I_eq_star_LU : D.star (D.I g) = D.star (D.L ⊔ D.U) := by
  apply le_antisymm (binary_star_mono d.I_le_LU)
  intro q hq
  have hm : d.model ⟨q, hq⟩ ∈ d.modelImage (D.I g) := by
    rw [d.modelImage_I_eq_top]
    trivial
  rw [d.modelImage_eq_star (D.I g) d.I_le_LU] at hm
  obtain ⟨a, ha, he⟩ := hm
  have heq : a = ⟨q, hq⟩ := d.model.injective he
  rw [heq] at ha
  exact ha

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
