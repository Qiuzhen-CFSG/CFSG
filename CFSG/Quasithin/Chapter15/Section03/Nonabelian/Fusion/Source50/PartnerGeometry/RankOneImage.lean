module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PlaneGeometry

/-!
# The actual rank-one subgroup in the determinant quotient

The original quotient map carries the selected pair of point stabilizers to
SL₂(2) times the opposite point involution. All image equalities here use that
same quotient map, so its kernel remains the original two-core.
Source: Aschbacher–Smith 15.3.56(3), printed p.1147.
-/
@[expose] public noncomputable section
open Subgroup ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G}
  {g : G} (d : Hypothesis D g)

def matrixSection : D.I g →* PairSL (F := ZMod 2) :=
  d.quotientMatrixEquiv.toMonoidHom.comp (QuotientGroup.mk' _)

def matrixImage (A : Subgroup G) : Subgroup (PairSL (F := ZMod 2)) :=
  (A.subgroupOf (D.I g)).map (matrixSection d)

theorem matrixImage_eq_modelImage (A : Subgroup G) : matrixImage d A = d.modelImage A := by
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨inclusion d.I_le_LU u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, d.I_eq_LU.symm ▸ u.property⟩, hu, ?_⟩
    rfl

theorem matrixSection_ker : (matrixSection d).ker = pCore 2 (D.I g) := by
  ext i
  change d.quotientMatrixEquiv (QuotientGroup.mk' _ i) = 1 ↔ _
  rw [d.quotientMatrixEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff _

theorem matrixImage_sup (A B : Subgroup G) (hA : A ≤ D.I g) (hB : B ≤ D.I g) :
    matrixImage d (A ⊔ B) = matrixImage d A ⊔ matrixImage d B := by
  unfold matrixImage
  rw [subgroupOf_sup hA hB, Subgroup.map_sup]

theorem matrixImage_conjugate (A : Subgroup G) (hA : A ≤ D.I g) (y : D.I g) :
    matrixImage d (rightConjugate A (y : G)) =
      (matrixImage d A).map (MulAut.conj (matrixSection d y)⁻¹).toMonoidHom := by
  have he (u : D.I g) : matrixSection d (y⁻¹ * u * (y⁻¹)⁻¹) =
      MulAut.conj (matrixSection d y)⁻¹ (matrixSection d u) := by
    change matrixSection d (y⁻¹ * u * (y⁻¹)⁻¹) =
      (matrixSection d y)⁻¹ * matrixSection d u * ((matrixSection d y)⁻¹)⁻¹
    simp only [map_mul, map_inv]
  ext b
  constructor
  · rintro ⟨u, ⟨v, hv, hvu⟩, rfl⟩
    let v' : D.I g := ⟨v,hA hv⟩
    have hu : y⁻¹ * v' * (y⁻¹)⁻¹ = u := by
      apply Subtype.ext
      exact hvu
    exact ⟨matrixSection d v', ⟨v', hv, rfl⟩,
      (he v').symm.trans (congrArg _ hu)⟩
  · rintro ⟨_, ⟨u,hu,rfl⟩, rfl⟩
    exact ⟨y⁻¹*u*(y⁻¹)⁻¹, ⟨u,hu,rfl⟩, he u⟩

omit [Finite G] in
theorem selected_pair_le_I (y : D.I g) : D.I (y : G) ≤ D.I g := by
  apply sup_le le_sup_left
  rintro _ ⟨u, hu, rfl⟩
  exact (D.I g).mul_mem ((D.I g).mul_mem ((D.I g).inv_mem y.property)
    (mem_sup_left hu)) ((D.I g).inv_mem ((D.I g).inv_mem y.property))

theorem selected_pair_image (z : D.V₁) (hz : d.pointVector z ≠ 0) (y : D.I g)
    (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    matrixImage d (D.I (y : G)) = MatrixOrbit.rankOne (d.pointVector z) := by
  have hUy : rightConjugate D.U (y : G) ≤ D.I g :=
    le_sup_right.trans (selected_pair_le_I y)
  change matrixImage d (D.U ⊔ rightConjugate D.U (y : G)) = _
  rw [matrixImage_sup d _ _ le_sup_left hUy, matrixImage_conjugate d _ le_sup_left,
    hyc, matrixImage_eq_modelImage d D.U, d.modelImage_U_eq_vector_stabilizer z hz]
  exact MatrixOrbit.rankOne_generated _ hz (d.pointVector_det z)

theorem residual_join_image (z : D.V₁) (hz : d.pointVector z ≠ 0) (y : D.I g)
    (hy : (y : G) ∈ leftResidual d) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    matrixImage d (leftResidual d ⊔ D.U) = MatrixOrbit.rankOne (d.pointVector z) := by
  have hJK : D.I (y : G) ≤ leftResidual d ⊔ D.U := by
    apply sup_le le_sup_right
    rintro _ ⟨u, hu, rfl⟩
    exact (leftResidual d ⊔ D.U).mul_mem
      ((leftResidual d ⊔ D.U).mul_mem (mem_sup_left ((leftResidual d).inv_mem hy))
        (mem_sup_right hu)) (mem_sup_left ((leftResidual d).inv_mem ((leftResidual d).inv_mem hy)))
  apply le_antisymm
  · rw [matrixImage_sup d _ _ (leftResidual_le_I d) le_sup_left]
    apply sup_le
    · rintro _ ⟨i, hi, rfl⟩
      have hsecond := leftResidual_matrix_second d i hi
      change matrixAction (1,(matrixSection d i).2) (d.pointVector z) = _
      change (matrixSection d i).2 = 1 at hsecond
      rw [hsecond]
      change matrixHom (1 : PairSL (F := ZMod 2)) _ = _
      rw [map_one]
      rfl
    · rw [matrixImage_eq_modelImage d D.U, d.modelImage_U_eq_vector_stabilizer z hz,
        ← MatrixOrbit.rankOne_generated _ hz (d.pointVector_det z)]
      exact le_sup_left
  · rw [← selected_pair_image d z hz y hyc]
    exact map_mono (comap_mono hJK)

theorem selected_pair_normalizes_plane (y : D.I g)
    (hy : (y : G) ∈ leftResidual d) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    D.I (y : G) ≤ normalizer (localSpan D.V₁ (leftResidual d) : Set G) := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  rw [(selected_plane_eq d z hz y hy hyc).2]
  intro i hi
  apply normalizes_liftedPlane d z hz ⟨i, selected_pair_le_I y hi⟩
  rw [← selected_pair_image d z hz y hyc]
  exact ⟨⟨i,selected_pair_le_I y hi⟩,hi,rfl⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
