module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.Model
public import Theory.AtlasPort.OtherSporadic.Algebra.SymmetricMatrixSpace
public import Mathlib.LinearAlgebra.Pi

/-!
# A faithful matrix-block action of the full SL3 group

The space consists of all 3-by-3 matrices, seven fixed coordinates, and three
copies each of symmetric matrices and their duals. The action is conjugation
on the first block and congruence on the symmetric blocks. Its dimension is
52. If an element acts trivially, conjugation makes it scalar; the symmetric
block and determinant then give c² = c³ = 1, hence c = 1.

The full matrix block retains diagonal coordinates in characteristic three.
No trace-zero splitting, division by three, or irreducibility is used. The
comparison with the literal F4 Geck lattice remains a separate change-of-basis
problem, consumed by `SourceModel.Transport`; this module does not assert it.
The source route is GLS3 §2.6.2, the common-lattice subsystem construction,
used in Aschbacher--Smith A.2.17, printed p.39.

The symmetric-matrix carrier reuses the attributed ATLAS port
`Theory/AtlasPort/OtherSporadic/Algebra/SymmetricMatrixSpace.lean`;
its attribution and license remain there and in `LICENSES/ATLAS.txt`.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2.SourceBlocks
open Matrix Atlas.Algebra
variable (F : Type*) [Field F]

/-- The full matrix block, including its diagonal lattice. -/
abbrev Mat := Matrix (Fin 3) (Fin 3) F
/-- Actual symmetric matrices, with their inherited linear structure. -/
abbrev Sym := symmetricMatrixSpace F (Fin 3)
/-- The concrete block carrier for the short A2 lattice comparison. -/
abbrev Space := Mat F × (Fin 7 → F) × (Fin 3 → Sym F) × (Fin 3 → Sym F)

theorem space_finrank : Module.finrank F (Space F) = 52 := by
  simp [Space, Mat, Sym, Module.finrank_prod, Module.finrank_pi_fintype,
    Module.finrank_matrix, symmetricMatrixSpace_finrank, Nat.choose]

/-- Congruence preserves the actual symmetric subspace. -/
def congruence (A : Mat F) : Sym F →ₗ[F] Sym F where
  toFun X := ⟨A * X.val * A.transpose, by
    apply (mem_symmetricMatrixSpace_iff _).mpr
    have hx := (mem_symmetricMatrixSpace_iff _).mp X.property
    change (A * X.val * A.transpose).transpose = _
    rw [transpose_mul, transpose_mul, transpose_transpose, hx, Matrix.mul_assoc]⟩
  map_add' X Y := by apply Subtype.ext; simp [mul_add, add_mul]
  map_smul' c X := by apply Subtype.ext; simp

@[simp] theorem congruence_apply (A : Mat F) (X : Sym F) :
    (congruence F A X).val = A * X.val * A.transpose := rfl

theorem congruence_mul (A B : Mat F) (X : Sym F) :
    congruence F (A * B) X = congruence F A (congruence F B X) := by
  apply Subtype.ext
  simp only [congruence_apply, transpose_mul, Matrix.mul_assoc]

@[simp] theorem congruence_one (X : Sym F) : congruence F 1 X = X := by
  apply Subtype.ext
  simp

/-- Conjugation, the fixed block, and natural and dual congruence. -/
def linear (g : Model F) : Space F →ₗ[F] Space F where
  toFun v := (g.val * v.1 * (g⁻¹).val, v.2.1,
    fun i => congruence F g.val (v.2.2.1 i),
    fun i => congruence F (g⁻¹).val.transpose (v.2.2.2 i))
  map_add' v w := by
    apply Prod.ext
    · simp [mul_add, add_mul]
    · exact Prod.ext rfl (Prod.ext (by funext i; exact map_add (congruence F _) _ _)
        (by funext i; exact map_add (congruence F _) _ _))
  map_smul' c v := by
    apply Prod.ext
    · simp
    · exact Prod.ext rfl (Prod.ext (by funext i; exact map_smul (congruence F _) _ _)
        (by funext i; exact map_smul (congruence F _) _ _))

theorem linear_one : linear F 1 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp [linear]

theorem linear_mul (g h : Model F) :
    linear F (g * h) = (linear F g).comp (linear F h) := by
  apply LinearMap.ext
  intro v
  simp only [linear, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_))
  · simp only [Matrix.mul_assoc]
  · funext i
    exact congruence_mul F g.val h.val _
  · funext i
    rw [transpose_mul]
    exact congruence_mul F _ _ _

/-- The genuine group action; its inverse is the action of the inverse matrix. -/
def action : Model F →* (Space F ≃ₗ[F] Space F) where
  toFun g := LinearEquiv.ofLinearMap (linear F g) (linear F g⁻¹)
    (by rw [← linear_mul, mul_inv_cancel, linear_one])
    (by rw [← linear_mul, inv_mul_cancel, linear_one])
  map_one' := by apply LinearEquiv.toLinearMap_injective; exact linear_one F
  map_mul' g h := by apply LinearEquiv.toLinearMap_injective; exact linear_mul F g h

@[simp] theorem action_apply (g : Model F) (v : Space F) : action F g v =
    (g.val * v.1 * (g⁻¹).val, v.2.1,
      fun i => congruence F g.val (v.2.2.1 i),
      fun i => congruence F (g⁻¹).val.transpose (v.2.2.2 i)) := rfl

/-- Both scalar conditions are used, so this is faithful on full SL3. -/
theorem action_injective : Function.Injective (action F) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have he : action F g = 1 := hg
  have hc (X : Mat F) : g.val * X * (g⁻¹).val = X :=
    congrArg Prod.fst (DFunLike.congr_fun he (X, 0, 0, 0))
  have hcomm (X : Mat F) : g.val * X = X * g.val := by
    have h := congrArg (· * g.val) (hc X)
    simpa only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, mul_one] using h
  have hz : g ∈ Subgroup.center (Model F) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact (hcomm h.val).symm
  obtain ⟨c, hcube, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hcube' : c ^ 3 = 1 := by simpa using hcube
  let I : Sym F := ⟨1, (mem_symmetricMatrixSpace_iff _).mpr isSymm_one⟩
  have hs : congruence F g.val I = I :=
    congrArg (fun v : Space F => v.2.2.1 0)
      (DFunLike.congr_fun he (0, 0, fun _ => I, 0))
  have hs0 := congrArg (fun X : Sym F => X.val 0 0) hs
  have hsquare : c * c = 1 := by
    simpa only [congruence_apply, ← hscalar, I, scalar_apply, diagonal_transpose,
      diagonal_mul, mul_diagonal, diagonal_apply_eq, one_apply_eq, mul_one] using hs0
  have hc1 : c = 1 := by
    calc
      c = c * (c * c) := by rw [hsquare, mul_one]
      _ = c ^ 3 := by ring
      _ = 1 := hcube'
  apply Subtype.ext
  simpa only [hc1, map_one, Matrix.SpecialLinearGroup.coe_one] using hscalar.symm

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2.SourceBlocks
