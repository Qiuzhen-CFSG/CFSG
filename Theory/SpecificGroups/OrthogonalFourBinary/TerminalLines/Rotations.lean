module

public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# The two-residual of the binary orthogonal four-group

The independent order-three rotations of the two definite planes form a
commutative normal subgroup. A kernel-checked enumeration of the images of
four basis vectors expresses every isometry by rotations, plane reflections
and plane interchange. It proves that each fourth power lies in the rotation
subgroup, so its quotient is a two-group. The rotations themselves have odd
order, identifying this subgroup with the intrinsic two-residual.

All calculations concern the existing quadratic form and its actual linear
isometries. No abstract group identification is substituted for the action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the orthogonal
space and residual on printed pp.1121–1122; applied to the line product on
p.1154. The basis-enumeration method follows the independent
`OrthogonalFourBinary.IndexTwoNormalizer.Geometry` calculation.
-/

@[expose] public section

set_option synthInstance.maxSize 10000

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.TerminalLines

abbrev RotationCode := Multiplicative (ZMod 3 × ZMod 3)

def planeRotation : Plane ≃ₗ[F] Plane where
  toFun x := (x.2, x.1 + x.2)
  invFun x := (x.1 + x.2, x.1)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def rotation (i : RotationCode) : Space ≃ₗ[F] Space :=
  (planeRotation ^ i.toAdd.1.val).prodCongr (planeRotation ^ i.toAdd.2.val)

private theorem rotation_form : ∀ i : RotationCode, ∀ w : Space,
    form (rotation i w) = form w := by decide +kernel

def rotationHom : RotationCode →* IsometryGroup where
  toFun i := ⟨rotation i, by
    exact (mem_quadraticIsometrySubgroup form _).mpr (rotation_form i)⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact (show ∀ w : Space, rotation 1 w = w from by decide +kernel)
  map_mul' := by
    intro i j
    apply Subtype.ext
    apply LinearEquiv.ext
    exact (show ∀ i j : RotationCode, ∀ w : Space,
      rotation (i*j) w = rotation i (rotation j w) from by decide +kernel) i j

def rotations : Subgroup IsometryGroup := rotationHom.range

instance rotations_commutative : IsMulCommutative rotations := by
  change IsMulCommutative rotationHom.range
  infer_instance

theorem rotation_cube (i : RotationCode) : rotationHom i ^ 3 = 1 := by
  rw [← map_pow]
  have h : ∀ i : RotationCode, i ^ 3 = 1 := by decide +kernel
  rw [h, map_one]

private def planeFlip : Plane ≃ₗ[F] Plane := LinearEquiv.prodComm F F F
private def swap : Space ≃ₗ[F] Space := LinearEquiv.prodComm F Plane Plane
private abbrev FullCode := RotationCode × (Fin 2 × Fin 2 × Fin 2)
private def candidate (i : FullCode) : Space ≃ₗ[F] Space :=
  rotation i.1 * ((planeFlip ^ (i.2.1 : ℕ)).prodCongr
    (planeFlip ^ (i.2.2.1 : ℕ))) * swap ^ (i.2.2.2 : ℕ)

private def basis0 : Space := ((1,0),(0,0))
private def basis1 : Space := ((0,1),(0,0))
private def basis2 : Space := ((0,0),(1,0))
private def basis3 : Space := ((0,0),(0,1))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem exhaustive : ∀ a b c d : Space,
    form a = 1 ∧ form b = 1 ∧ form c = 1 ∧ form d = 1 ∧
    form (a+b) = 1 ∧ form (c+d) = 1 ∧
    form (a+c) = 0 ∧ form (a+d) = 0 ∧ form (b+c) = 0 ∧ form (b+d) = 0 →
    ∃ i : FullCode, a = candidate i basis0 ∧ b = candidate i basis1 ∧
      c = candidate i basis2 ∧ d = candidate i basis3 := by decide +kernel

private theorem space_expand (w : Space) :
    w = w.1.1 • basis0 + w.1.2 • basis1 + w.2.1 • basis2 + w.2.2 • basis3 := by
  have h : ∀ w : Space,
      w = w.1.1 • basis0 + w.1.2 • basis1 + w.2.1 • basis2 + w.2.2 • basis3 := by
    decide +kernel
  exact h w

private theorem basis_ext (e f : Space ≃ₗ[F] Space)
    (h0 : e basis0 = f basis0) (h1 : e basis1 = f basis1)
    (h2 : e basis2 = f basis2) (h3 : e basis3 = f basis3) : e = f := by
  apply LinearEquiv.ext
  intro w
  rw [space_expand w]
  simp only [map_add, map_smul, h0, h1, h2, h3]

private theorem exists_candidate (g : IsometryGroup) : ∃ i : FullCode, g.val = candidate i := by
  have hq := (mem_quadraticIsometrySubgroup form _).mp g.property
  obtain ⟨i,h0,h1,h2,h3⟩ := exhaustive
    (g.val basis0) (g.val basis1) (g.val basis2) (g.val basis3) (by
      simp only [← map_add, hq]
      decide +kernel)
  exact ⟨i,basis_ext _ _ h0 h1 h2 h3⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem conjugate_rotation : ∀ i : FullCode, ∀ j : RotationCode,
    ∃ k : RotationCode, ∀ w : Space,
      candidate i (rotation j w) = rotation k (candidate i w) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem candidate_fourth : ∀ i : FullCode, ∃ j : RotationCode, ∀ w : Space,
    (candidate i ^ 4) w = rotation j w := by decide +kernel

instance rotations_normal : rotations.Normal := by
  constructor
  rintro x ⟨j,rfl⟩ g
  obtain ⟨i,hi⟩ := exists_candidate g
  obtain ⟨k,hk⟩ := conjugate_rotation i j
  refine ⟨k, ?_⟩
  apply eq_mul_inv_iff_mul_eq.mpr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  change rotation k (g.val w) = g.val (rotation j w)
  rw [hi]
  exact (hk w).symm

theorem fourth_mem_rotations (g : IsometryGroup) : g ^ 4 ∈ rotations := by
  obtain ⟨i,hi⟩ := exists_candidate g
  obtain ⟨j,hj⟩ := candidate_fourth i
  refine ⟨j, ?_⟩
  apply Subtype.ext
  change rotation j = g.val ^ 4
  rw [hi]
  exact (LinearEquiv.ext hj).symm

theorem residual_eq_rotations : pResidual 2 IsometryGroup = rotations := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, ?_⟩
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective rotations q
    refine ⟨2, ?_⟩
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (fourth_mem_rotations g)
  · rintro g ⟨i,rfl⟩
    apply mem_pResidual_of_orderOf_coprime
    exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one (rotation_cube i))
      (by decide : Nat.Coprime 2 3)

theorem residual_commutative : IsMulCommutative (pResidual 2 IsometryGroup) := by
  rw [residual_eq_rotations]
  infer_instance

/-- A rotation of each definite plane is determined by its action on a fixed
nonzero singular vector, so the pair of rotations is faithful. -/
theorem rotationHom_injective : Function.Injective rotationHom := by
  have h : ∀ i j : RotationCode,
      rotation i ((1,0),(1,0)) = rotation j ((1,0),(1,0)) → i = j := by
    decide +kernel
  intro i j hij
  exact h i j (congrArg (fun g : IsometryGroup => g.val ((1,0),(1,0))) hij)

/-- The two-residual is the actual group of independent order-three plane
rotations, with its specified action retained. -/
noncomputable def residualEquiv : RotationCode ≃* pResidual 2 IsometryGroup :=
  (MonoidHom.ofInjective rotationHom_injective).trans
    (MulEquiv.subgroupCongr residual_eq_rotations.symm)

/-- The residual equivalence acts through the original plane rotations. -/
theorem residualEquiv_apply (i : RotationCode) :
    (residualEquiv i : IsometryGroup) = rotationHom i := rfl

end OrthogonalFourBinary.TerminalLines
