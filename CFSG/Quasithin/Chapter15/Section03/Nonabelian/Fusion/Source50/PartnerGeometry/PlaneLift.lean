module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Selection
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PlaneModel

/-!
# Lifting the selected cubic plane to the original natural subgroup

The coordinates of G.2.6 embed the finite orbit plane into the actual V.
The singular-plane calculation puts it in the original perpendicular
hyperplane and hence U. The same quotient projection transports its action.
Source: the opening rank-one construction of 15.3.56, printed p.1147.
-/

@[expose] public noncomputable section
open Subgroup
open ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G}
  {g : G} (d : Hypothesis D g)

def matrixLift : Multiplicative (Mat (F := ZMod 2)) →* G :=
  D.VL.subtype.comp d.coordinates.symm.toMonoidHom

theorem matrixLift_injective : Function.Injective (matrixLift d) :=
  D.VL.subtype_injective.comp d.coordinates.symm.injective

def liftedPlane (z : D.V₁) : Subgroup G :=
  (MatrixOrbit.orbitPlane (d.pointVector z)).map (matrixLift d)

theorem liftedPlane_le_VL (z : D.V₁) : liftedPlane d z ≤ D.VL := by
  rintro _ ⟨v, _, rfl⟩
  exact (d.coordinates.symm v).property

theorem liftedPlane_card (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    Nat.card (liftedPlane d z) = 4 :=
  (card_map_of_injective (matrixLift_injective d)).trans
    (MatrixOrbit.orbitPlane_card _ hz)

theorem point_le_liftedPlane (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    D.V₁ ≤ liftedPlane d z := by
  obtain ⟨a, ha, hall⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp d.point_card
  have hz1 : z ≠ 1 := fun he => hz ((d.pointVector_eq_zero_iff z).mpr he)
  have hzA := hall z hz1
  intro x hx
  by_cases h1 : x = 1
  · exact h1 ▸ (liftedPlane d z).one_mem
  have hxA := hall (⟨x,hx⟩ : D.V₁) (fun h => h1 (congrArg Subtype.val h))
  have hxz : x = (z : G) := congrArg Subtype.val (hxA.trans hzA.symm)
  rw [hxz]
  refine ⟨Multiplicative.ofAdd (d.pointVector z), MatrixOrbit.orbitPlane_first _, ?_⟩
  change (d.coordinates.symm (d.coordinates (inclusion (point_le_VL D) z)) : G) = z
  rw [d.coordinates.symm_apply_apply]
  rfl

theorem liftedPlane_le_perpendicular (z : D.V₁) : liftedPlane d z ≤ D.V := by
  rintro _ ⟨v, ⟨a, ha⟩, rfl⟩
  change (d.coordinates.symm v : G) ∈ D.V
  apply (d.perpendicular (d.coordinates.symm v)).mpr
  intro w
  rw [d.coordinates.apply_symm_apply]
  by_cases hz : d.pointVector z = 0
  · have hv : v = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← ha]
      change a.toAdd 0 • d.pointVector z + a.toAdd 1 • matrixAction MatrixOrbit.leftCubic
        (d.pointVector z) = 0
      simp [hz]
    rw [hv]
    simp
  obtain ⟨b, hb, hall⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp d.point_card
  have hz1 : z ≠ 1 := fun he => hz ((d.pointVector_eq_zero_iff z).mpr he)
  by_cases hw1 : w = 1
  · subst w
    have hzero : (d.coordinates ⟨(1 : D.V₁), point_le_VL D (one_mem _)⟩).toAdd = 0 := by
      change (d.coordinates 1).toAdd = 0
      rw [map_one]
      rfl
    rw [hzero]
    exact map_zero _
  have hwz : w = z := (hall w hw1).trans (hall z hz1).symm
  subst w
  change (determinantForm (F := ZMod 2)).polarBilin v.toAdd (d.pointVector z) = 0
  have hv : v.toAdd = a.toAdd 0 • d.pointVector z +
      a.toAdd 1 • matrixAction MatrixOrbit.leftCubic (d.pointVector z) :=
    (congrArg Multiplicative.toAdd ha).symm
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hv]
  have he : (a.toAdd 0 • d.pointVector z + a.toAdd 1 •
      matrixAction MatrixOrbit.leftCubic (d.pointVector z)) + d.pointVector z =
      (a.toAdd 0 + 1) • d.pointVector z + a.toAdd 1 •
        matrixAction MatrixOrbit.leftCubic (d.pointVector z) := by rw [add_smul, one_smul]; abel
  rw [he, MatrixOrbit.orbit_totally_singular _ (d.pointVector_det z),
    MatrixOrbit.orbit_totally_singular _ (d.pointVector_det z), d.pointVector_singular z]
  simp

theorem matrixLift_equivariant (i : D.I g) (v : Multiplicative (Mat (F := ZMod 2))) :
    matrixLift d (Multiplicative.ofAdd
      (matrixAction (d.quotientMatrixEquiv (QuotientGroup.mk' _ i)) v.toAdd)) =
      (i : G) * matrixLift d v * (i : G)⁻¹ := by
  simpa only [matrixLift, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulEquiv.apply_symm_apply, subtype_apply] using
    d.quotientMatrixEquiv_equivariant i (d.coordinates.symm v)

theorem normalizes_liftedPlane (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (i : D.I g)
    (hi : d.quotientMatrixEquiv (QuotientGroup.mk' _ i) ∈ MatrixOrbit.rankOne (d.pointVector z)) :
    (i : G) ∈ normalizer (liftedPlane d z : Set G) := by
  apply (mem_normalizer_iff).mpr
  intro x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨_, MatrixOrbit.rankOne_preserves_plane _ hz (d.pointVector_det z) ⟨_,hi⟩ v hv, ?_⟩
    exact matrixLift_equivariant d i v
  · intro hx
    have hii : d.quotientMatrixEquiv (QuotientGroup.mk' _ i⁻¹) ∈
        MatrixOrbit.rankOne (d.pointVector z) := by
      rw [map_inv, map_inv]
      exact inv_mem hi
    obtain ⟨v, hv, he⟩ := hx
    refine ⟨_, MatrixOrbit.rankOne_preserves_plane _ hz (d.pointVector_det z) ⟨_,hii⟩ v hv, ?_⟩
    rw [matrixLift_equivariant, he]
    change (i : G)⁻¹ * ((i : G) * x * (i : G)⁻¹) * ((i : G)⁻¹)⁻¹ = x
    group

/-- The chosen residual is literally in the first matrix factor. -/
theorem leftResidual_matrix_second (i : D.I g) (hi : (i : G) ∈ leftResidual d) :
    (d.quotientMatrixEquiv (QuotientGroup.mk' _ i)).2 = 1 := by
  have hh := Chapter15Collapse.oddFactor_image_le
    (moduleProjection d.quotientSymmetricEquiv) D.L
    Representation.BinaryQuadraticPair.ProductDecomposition.leftFactor
      (mem_map_of_mem _ hi)
  have he : (d.quotientSymmetricEquiv (QuotientGroup.mk' _ i)).2 = 1 := hh.2
  change (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
    (d.quotientMatrixEquiv (QuotientGroup.mk' _ i)).2 = 1 at he
  exact (MulEquiv.map_eq_one_iff _).mp he

theorem leftResidual_normalizes_liftedPlane (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    leftResidual d ≤ normalizer (liftedPlane d z : Set G) := by
  intro i hi
  apply normalizes_liftedPlane d z hz ⟨i, leftResidual_le_I d hi⟩
  change matrixAction (1, (d.quotientMatrixEquiv (QuotientGroup.mk' _
    (⟨i, leftResidual_le_I d hi⟩ : D.I g))).2) (d.pointVector z) = d.pointVector z
  rw [leftResidual_matrix_second d _ hi]
  change matrixHom (1 : PairSL (F := ZMod 2)) (d.pointVector z) = d.pointVector z
  rw [map_one]
  rfl

/-- The source orbit span lies in this particular singular orbit plane. -/
theorem span_le_liftedPlane (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    localSpan D.V₁ (leftResidual d) ≤ liftedPlane d z :=
  conjugateSpanBy_le (point_le_liftedPlane d z hz)
    (leftResidual_normalizes_liftedPlane d z hz)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
