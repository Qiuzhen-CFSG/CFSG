module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Data.ZMod.Basic

/-!
# The matrix model of PSL₃(3)

The canonical projection from SL₃(3) to PSL₃(3) is an isomorphism. This lets
subgroup constructions and their completeness proofs use determinant-one
matrices before transporting them to the projective group.

The center consists of scalar matrices whose scalar has cube one, by
`Matrix.SpecialLinearGroup.mem_center_iff`. Over `ZMod 3` the only such scalar
is one; the latter three-element calculation is checked by kernel reduction.
-/

namespace Matrix.PSL3Three

/-- The determinant-one matrix model over the three-element field. -/
public abbrev SL := SpecialLinearGroup (Fin 3) (ZMod 3)

/-- The projective matrix model over the three-element field. -/
public abbrev PSL := ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)

/-- SL₃(3) has trivial center. -/
public theorem center_eq_bot : Subgroup.center SL = ⊥ := by
  apply eq_bot_iff.mpr
  intro mat hmat
  change mat = 1
  obtain ⟨scalar, hpower, hscalar⟩ := SpecialLinearGroup.mem_center_iff.mp hmat
  have hroot : ∀ scalar : ZMod 3, scalar ^ 3 = 1 → scalar = 1 := by decide
  have hscalarOne : scalar = 1 := hroot scalar (by simpa using hpower)
  apply Subtype.ext
  simpa [hscalarOne] using hscalar.symm

/-- The canonical projection, retaining the actual matrix quotient map. -/
@[expose] public def project : SL →* PSL := QuotientGroup.mk' _

public theorem project_injective : Function.Injective project := by
  rw [← MonoidHom.ker_eq_bot_iff, project, QuotientGroup.ker_mk', center_eq_bot]

public theorem project_surjective : Function.Surjective project :=
  QuotientGroup.mk'_surjective _

/-- The canonical projection identifies SL₃(3) with PSL₃(3). -/
public noncomputable def equiv : SL ≃* PSL :=
  MulEquiv.ofBijective project ⟨project_injective, project_surjective⟩

@[simp] public theorem equiv_apply (g : SL) : equiv g = project g := by
  unfold equiv
  rfl

end Matrix.PSL3Three
