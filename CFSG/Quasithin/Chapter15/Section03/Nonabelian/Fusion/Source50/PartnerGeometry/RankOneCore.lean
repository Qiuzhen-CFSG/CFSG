module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.RankOneImage
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# The actual rank-one plane kernel

Restricting the original determinant quotient to J gives S₃ times a right
point involution. Its left projection is the action on the selected plane.
The two-group kernel is exactly O₂(J), and the original pair core has index
two in it. These supply the chief-length comparison in 15.3.56(3).
-/
@[expose] public noncomputable section
open Subgroup ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G}
  {g : G} (d : Hypothesis D g)

private theorem rankOneLeft_kernel_card (X : MatrixOrbit.M) (hX : X ≠ 0)
    (hs : X.det = 0) : Nat.card (MatrixOrbit.rankOneLeft X).ker = 2 := by
  have hc := (MatrixOrbit.rankOneLeft X).ker.card_mul_index
  have hsix : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Nat.card_congr (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [index_ker, MonoidHom.range_eq_top.mpr (MatrixOrbit.rankOneLeft_surjective X),
    Nat.card_congr (topEquiv.toEquiv), hsix, MatrixOrbit.rankOne_card X hX hs] at hc
  omega

def selectedPairActor (z : D.V₁) (hz : d.pointVector z ≠ 0) (y : D.I g)
    (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    D.I (y : G) →* MatrixOrbit.rankOne (d.pointVector z) :=
  ((matrixSection d).comp (inclusion (selected_pair_le_I y))).codRestrict _ (by
    intro j
    rw [← selected_pair_image d z hz y hyc]
    exact ⟨inclusion (selected_pair_le_I y) j,j.property,rfl⟩)

theorem selectedPairActor_surjective (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    Function.Surjective (selectedPairActor d z hz y hyc) := by
  intro a
  have ha : (a : MatrixOrbit.P) ∈ matrixImage d (D.I (y : G)) := by
    simpa only [selected_pair_image d z hz y hyc] using a.property
  obtain ⟨i,hi,he⟩ := ha
  exact ⟨⟨i,hi⟩,Subtype.ext he⟩

theorem selectedPairActor_ker (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    (selectedPairActor d z hz y hyc).ker =
      (pCore 2 (D.I g)).comap (inclusion (selected_pair_le_I y)) := by
  ext j
  change (selectedPairActor d z hz y hyc j = 1) ↔ _
  rw [Subtype.ext_iff]
  change matrixSection d (inclusion (selected_pair_le_I y) j) = 1 ↔ _
  rw [← matrixSection_ker d]
  rfl

def selectedPlaneActor (z : D.V₁) (hz : d.pointVector z ≠ 0) (y : D.I g)
    (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    D.I (y : G) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  (MatrixOrbit.rankOneLeft (d.pointVector z)).comp (selectedPairActor d z hz y hyc)

theorem selectedPlaneActor_surjective (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    Function.Surjective (selectedPlaneActor d z hz y hyc) :=
  (MatrixOrbit.rankOneLeft_surjective _).comp (selectedPairActor_surjective d z hz y hyc)

theorem selectedPlaneActor_kernel_two (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    IsPGroup 2 (selectedPlaneActor d z hz y hyc).ker := by
  have hk : IsPGroup 2 (selectedPairActor d z hz y hyc).ker := by
    rw [selectedPairActor_ker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hc : IsPGroup 2 (MatrixOrbit.rankOneLeft (d.pointVector z)).ker :=
    IsPGroup.of_card (n := 1) (rankOneLeft_kernel_card _ hz (d.pointVector_det z))
  change IsPGroup 2 ((MatrixOrbit.rankOneLeft (d.pointVector z)).comp
    (selectedPairActor d z hz y hyc)).ker
  rw [← MonoidHom.comap_ker]
  exact hc.comap_of_ker_isPGroup _ hk

theorem selectedPlaneActor_ker_eq_core (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    (selectedPlaneActor d z hz y hyc).ker = pCore 2 (D.I (y : G)) := by
  let e := Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three
  let φ := e.toMonoidHom.comp (selectedPlaneActor d z hz y hyc)
  have he : φ.ker = (selectedPlaneActor d z hz y hyc).ker := by
    ext j
    change e (selectedPlaneActor d z hz y hyc j) = 1 ↔ _
    rw [e.map_eq_one_iff]
    rfl
  rw [← he]
  apply ker_eq_twoCore_of_surjective_perm_three φ
    (e.surjective.comp (selectedPlaneActor_surjective d z hz y hyc))
  rw [he]
  exact selectedPlaneActor_kernel_two d z hz y hyc

private theorem matrix_fix_iff_commute (i : D.I g)
    (v : Multiplicative MatrixOrbit.M) :
    matrixAction (matrixSection d i) v.toAdd = v.toAdd ↔
      Commute (i : G) (matrixLift d v) := by
  have he := matrixLift_equivariant d i v
  constructor
  · intro h
    change matrixLift d (Multiplicative.ofAdd (matrixAction (matrixSection d i) v.toAdd)) = _ at he
    rw [h] at he
    change i.val * matrixLift d v = matrixLift d v * i.val
    exact (mul_inv_eq_iff_eq_mul).mp he.symm
  · intro h
    apply Multiplicative.ofAdd.injective
    apply matrixLift_injective d
    change matrixLift d (Multiplicative.ofAdd (matrixAction (matrixSection d i) v.toAdd)) = _ at he
    rw [he]
    calc
      (i : G) * matrixLift d v * (i : G)⁻¹ =
          matrixLift d v * (i : G) * (i : G)⁻¹ := congrArg (fun x => x * (i : G)⁻¹) h.eq
      _ = matrixLift d v := by group

/-- The left projection is exactly the pointwise action on the actual orbit plane. -/
theorem selectedPlaneActor_ker_centralizer (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hy : (y : G) ∈ leftResidual d)
    (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    (selectedPlaneActor d z hz y hyc).ker =
      (D.I (y : G) ⊓ centralizer (localSpan D.V₁ (leftResidual d) : Set G)).subgroupOf
        (D.I (y : G)) := by
  have hs := (selected_plane_eq d z hz y hy hyc).2
  ext j
  have hp := MatrixOrbit.rankOne_plane_kernel (d.pointVector z) hz
    (selectedPairActor d z hz y hyc j)
  change selectedPlaneActor d z hz y hyc j = 1 ↔
    ((j : G) ∈ D.I (y : G) ∧ (j : G) ∈ centralizer (localSpan D.V₁ (leftResidual d) : Set G))
  rw [and_iff_right j.property]
  change (selectedPairActor d z hz y hyc j).val.1 = 1 ↔ _
  rw [← hp,hs]
  constructor
  · intro h x hx
    obtain ⟨v,hv,rfl⟩ := hx
    exact ((matrix_fix_iff_commute d (inclusion (selected_pair_le_I y) j) v).mp (h v hv)).eq.symm
  · intro h v hv
    exact (matrix_fix_iff_commute d (inclusion (selected_pair_le_I y) j) v).mpr
      (h _ (mem_map_of_mem (matrixLift d) hv)).symm

/-- The literal pair core is its plane centralizer. -/
theorem selected_pair_core_centralizer (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hy : (y : G) ∈ leftResidual d)
    (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    (D.I (y : G)).pCoreIn 2 =
      D.I (y : G) ⊓ centralizer (localSpan D.V₁ (leftResidual d) : Set G) := by
  change (pCore 2 (D.I (y : G))).map (D.I (y : G)).subtype = _
  rw [← selectedPlaneActor_ker_eq_core d z hz y hyc,
    selectedPlaneActor_ker_centralizer d z hz y hy hyc, map_subgroupOf_eq_of_le inf_le_left]

/-- The original rank-one quotient is S₃. -/
def selected_pair_quotient (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    (D.I (y : G) ⧸ pCore 2 (D.I (y : G))) ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq (selectedPlaneActor_ker_eq_core d z hz y hyc).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (selectedPlaneActor d z hz y hyc)
      (selectedPlaneActor_surjective d z hz y hyc)).trans
        (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))

private theorem selectedPairActor_ker_map (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    (selectedPairActor d z hz y hyc).ker.map (D.I (y : G)).subtype =
      D.S g ⊓ D.I (y : G) := by
  rw [selectedPairActor_ker]
  ext x
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨⟨inclusion (selected_pair_le_I y) j,hj,rfl⟩,j.property⟩
  · rintro ⟨⟨i,hi,he⟩,hx⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    change inclusion (selected_pair_le_I y) ⟨x,hx⟩ ∈ pCore 2 (D.I g)
    have hei : inclusion (selected_pair_le_I y) ⟨x,hx⟩ = i := Subtype.ext he.symm
    rw [hei]
    exact hi

/-- The common old-core intersection has index two in the actual new core. -/
theorem selected_pair_core_bridge (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    (D.S g ⊓ D.I (y : G)).relIndex ((D.I (y : G)).pCoreIn 2) = 2 := by
  have himage : (pCore 2 (D.I (y : G))).map (selectedPairActor d z hz y hyc) =
      (MatrixOrbit.rankOneLeft (d.pointVector z)).ker := by
    rw [← selectedPlaneActor_ker_eq_core d z hz y hyc]
    change (((MatrixOrbit.rankOneLeft (d.pointVector z)).comp
      (selectedPairActor d z hz y hyc)).ker).map (selectedPairActor d z hz y hyc) = _
    rw [← MonoidHom.comap_ker, map_comap_eq_self_of_surjective
      (selectedPairActor_surjective d z hz y hyc)]
  rw [← selectedPairActor_ker_map d z hz y hyc]
  change ((selectedPairActor d z hz y hyc).ker.map (D.I (y : G)).subtype).relIndex
    ((pCore 2 (D.I (y : G))).map (D.I (y : G)).subtype) = _
  rw [relIndex_map_map_of_injective _ _ (D.I (y : G)).subtype_injective,
    relIndex_ker,himage]
  exact rankOneLeft_kernel_card _ hz (d.pointVector_det z)

/-- The new core is in the original Sylow subgroup: its only nontrivial
old matrix image is the right point involution, already present in U. -/
theorem selected_pair_core_le_T (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    (D.I (y : G)).pCoreIn 2 ≤ D.T := by
  rintro x ⟨j,hj,rfl⟩
  let i := inclusion (selected_pair_le_I y) j
  have hfirst : (matrixSection d i).1 = 1 := by
    change selectedPlaneActor d z hz y hyc j = 1
    change j ∈ (selectedPlaneActor d z hz y hyc).ker
    rw [selectedPlaneActor_ker_eq_core]
    exact hj
  have hright := (selectedPairActor d z hz y hyc j).property
  have himage : matrixSection d i ∈ matrixImage d D.U := by
    rw [matrixImage_eq_modelImage, d.modelImage_U_eq_vector_stabilizer z hz]
    change matrixAction ((matrixSection d i).1,(matrixSection d i).2) (d.pointVector z) = _
    rw [hfirst]
    exact hright
  obtain ⟨u,hu,he⟩ := himage
  have hku : i * u⁻¹ ∈ pCore 2 (D.I g) := by
    rw [← matrixSection_ker d]
    change matrixSection d (i*u⁻¹) = 1
    rw [map_mul,map_inv,← he,mul_inv_cancel]
  have hprod : (i : G) * (u : G)⁻¹ ∈ D.T :=
    d.S_le_T ⟨i*u⁻¹,hku,rfl⟩
  have huT : (u : G) ∈ D.T := d.closure.normal.1 hu
  have hx := D.T.mul_mem hprod huT
  change (i : G) ∈ D.T
  simpa only [inv_mul_cancel_right] using hx

/-- All three literal inputs consumed by the source chief-length comparison. -/
theorem selected_rank_one_core (y : D.I g) (hy : (y : G) ∈ leftResidual d)
    (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    Nonempty ((D.I (y : G) ⧸ pCore 2 (D.I (y : G))) ≃* Equiv.Perm (Fin 3)) ∧
      (D.I (y : G)).pCoreIn 2 =
        D.I (y : G) ⊓ centralizer (localSpan D.V₁ (leftResidual d) : Set G) ∧
      (D.S g ⊓ D.I (y : G)).relIndex ((D.I (y : G)).pCoreIn 2) = 2 := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  exact ⟨⟨selected_pair_quotient d z hz y hyc⟩,
    selected_pair_core_centralizer d z hz y hy hyc,
    selected_pair_core_bridge d z hz y hyc⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
