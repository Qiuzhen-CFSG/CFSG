module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PlaneLift
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The selected source plane is ZZʸ

The chosen cubic moves the original point, while its orbit plane has four
elements and is normalized by the original first residual factor. Counting
the two distinct point subgroups identifies that plane with ZZʸ and with
the entire Y₁-orbit span. These are the literal point-plane markings of
15.3.56(3), printed p.1147.
-/

@[expose] public noncomputable section
open Subgroup ClassicalOrthogonal.FourPlusMatrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G}
  {g : G} (d : Hypothesis D g)

theorem point_disjoint_selected_conjugate (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g)
    (hyc : d.quotientMatrixEquiv (QuotientGroup.mk' _ y) = MatrixOrbit.leftCubic) :
    Disjoint D.V₁ (rightConjugate D.V₁ (y : G)) := by
  obtain ⟨a, ha, hall⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp d.point_card
  have hz1 : z ≠ 1 := fun he => hz ((d.pointVector_eq_zero_iff z).mpr he)
  have hmove : (y : G)⁻¹ * z * (y : G) ≠ z := by
    intro he
    have hv : matrixAction MatrixOrbit.leftCubic⁻¹ (d.pointVector z) = d.pointVector z := by
      apply Multiplicative.ofAdd.injective
      apply matrixLift_injective d
      have hh := matrixLift_equivariant d y⁻¹ (Multiplicative.ofAdd (d.pointVector z))
      rw [map_inv, map_inv, hyc] at hh
      have hpoint : matrixLift d (Multiplicative.ofAdd (d.pointVector z)) = (z : G) := by
        change (d.coordinates.symm (d.coordinates (inclusion (point_le_VL D) z)) : G) = z
        rw [d.coordinates.symm_apply_apply]
        rfl
      rw [hpoint] at hh ⊢
      exact hh.trans (by simpa only [coe_inv, inv_inv] using he)
    apply MatrixOrbit.cubic_moves _ hz
    have hh := congrArg (matrixAction MatrixOrbit.leftCubic) hv
    have hc : matrixAction MatrixOrbit.leftCubic
        (matrixAction MatrixOrbit.leftCubic⁻¹ (d.pointVector z)) = d.pointVector z := by
      change matrixHom MatrixOrbit.leftCubic
        (matrixHom MatrixOrbit.leftCubic⁻¹ (d.pointVector z)) = _
      rw [map_inv]
      exact (matrixHom MatrixOrbit.leftCubic).apply_symm_apply _
    exact (hh.symm.trans hc)
  apply disjoint_def.mpr
  intro x hx hxY
  by_contra hnon
  have hxz : x = (z : G) := congrArg Subtype.val
    ((hall (⟨x,hx⟩ : D.V₁) (fun h => hnon (congrArg Subtype.val h))).trans
      (hall z hz1).symm)
  obtain ⟨w, hw, he⟩ := hxY
  have hw1 : w ≠ 1 := by
    intro h
    apply hnon
    rw [h] at he
    simpa only [map_one] using he.symm
  have hwz : w = (z : G) := congrArg Subtype.val
    ((hall (⟨w,hw⟩ : D.V₁) (fun h => hw1 (congrArg Subtype.val h))).trans
      (hall z hz1).symm)
  apply hmove
  change (y : G)⁻¹ * w * ((y : G)⁻¹)⁻¹ = x at he
  simpa only [hwz, inv_inv, hxz] using he

theorem selected_plane_eq (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hy : (y : G) ∈ leftResidual d)
    (hyc : d.quotientMatrixEquiv (QuotientGroup.mk' _ y) = MatrixOrbit.leftCubic) :
    liftedPlane d z = D.V₁ ⊔ rightConjugate D.V₁ (y : G) ∧
      localSpan D.V₁ (leftResidual d) = liftedPlane d z := by
  have hpoint := point_le_liftedPlane d z hz
  have hyn := leftResidual_normalizes_liftedPlane d z hz hy
  have hpointY : rightConjugate D.V₁ (y : G) ≤ liftedPlane d z := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_normalizer_iff.mp ((normalizer (liftedPlane d z : Set G)).inv_mem hyn) v).mp
      (hpoint hv)
  have hdis := point_disjoint_selected_conjugate d z hz y hyc
  let := d.VL_elementary
  have hnorm : rightConjugate D.V₁ (y : G) ≤ normalizer (D.V₁ : Set G) :=
    (hpointY.trans (liftedPlane_le_VL d z)).trans
      ((D.VL.le_centralizer.trans (centralizer_le (point_le_VL D))).trans
        (centralizer_le_normalizer (D.V₁ : Set G)))
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint D.V₁
    (rightConjugate D.V₁ (y : G)) hnorm hdis
  have hycard : Nat.card (rightConjugate D.V₁ (y : G)) = Nat.card D.V₁ :=
    card_map_of_injective (MulAut.conj (y : G)⁻¹).injective
  rw [hycard, d.point_card] at hc
  have he : D.V₁ ⊔ rightConjugate D.V₁ (y : G) = liftedPlane d z :=
    eq_of_le_of_card_ge (sup_le hpoint hpointY) (by rw [hc, liftedPlane_card d z hz])
  refine ⟨he.symm, ?_⟩
  apply le_antisymm (span_le_liftedPlane d z hz)
  rw [← he]
  apply sup_le (le_conjugateSpanBy _ _)
  rintro _ ⟨v, hv, rfl⟩
  exact subset_closure ⟨(y : G)⁻¹, (leftResidual d).inv_mem hy, v, hv, rfl⟩

/-- The complete literal plane marking for the selected source cubic. -/
theorem selected_plane (y : D.I g) (hy : (y : G) ∈ leftResidual d)
    (hyc : d.quotientMatrixEquiv (QuotientGroup.mk' _ y) = MatrixOrbit.leftCubic) :
    localSpan D.V₁ (leftResidual d) = D.V₁ ⊔ rightConjugate D.V₁ (y : G) ∧
      localSpan D.V₁ (leftResidual d) ≤ D.V ∧
      Nat.card (localSpan D.V₁ (leftResidual d)) = 4 ∧
      (y : G) ∈ normalizer (localSpan D.V₁ (leftResidual d) : Set G) ∧
      Disjoint D.V₁ (rightConjugate D.V₁ (y : G)) := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  obtain ⟨hp,hs⟩ := selected_plane_eq d z hz y hy hyc
  rw [hs]
  exact ⟨hp, liftedPlane_le_perpendicular d z, liftedPlane_card d z hz,
    leftResidual_normalizes_liftedPlane d z hz hy,
    point_disjoint_selected_conjugate d z hz y hyc⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
