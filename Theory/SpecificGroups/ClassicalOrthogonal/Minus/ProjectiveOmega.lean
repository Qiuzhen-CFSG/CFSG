module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ClassicalPointGroups
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# The scalar quotient of the orthogonal commutator group

The orthogonal group consists of linear transformations preserving a quadratic
form. We take its commutator subgroup and divide by precisely the scalar
transformations it contains. This is the definition of the projective Omega
construction used for the finite minus family (dimension at least four).
It is not the full orthogonal group, nor the determinant-one subgroup.

The scalar subgroup is central because linear maps commute with scalar
multiplication. Finiteness follows from the embedding of linear equivalences
into the functions on the finite vector space. The quotient therefore needs
no group-recognition or classification premise.

Source: GLS, *The Classification of the Finite Simple Groups*, volume 3,
§2.7 (`refs/KGroup/GLS3/chapter2.tex`). The split four-dimensional group over
`F₂` has a special Omega convention; this generic construction is used here
only for the minus family, which has no such exception.
-/

@[expose] public section

namespace ClassicalOrthogonal.Minus
universe u
variable (F V : Type u) [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- The full group of isometries of the quadratic form. -/
abbrev Orthogonal := Theory.AlgebraicGroup.quadraticIsometrySubgroup Q
/-- The orthogonal commutator subgroup. -/
abbrev Omega := commutator (Orthogonal F V Q)

/-- Scalar transformations lying in the orthogonal commutator subgroup. -/
def scalarSubgroup : Subgroup (Omega F V Q) where
  carrier := {g | ∃ c : Fˣ, ∀ v : V, g.val.val v = (c : F) • v}
  one_mem' := ⟨1, fun _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨c,hc⟩ ⟨d,hd⟩
    refine ⟨c*d, fun v => ?_⟩
    change g.val.val (h.val.val v) = _
    rw [hc, hd]
    simp [mul_smul]
  inv_mem' := by
    rintro g ⟨c,hc⟩
    refine ⟨c⁻¹, fun v => ?_⟩
    apply g.val.val.injective
    change g.val.val (g.val.val.symm v) = g.val.val ((↑(c⁻¹) : F) • v)
    rw [LinearEquiv.apply_symm_apply]
    rw [hc, smul_smul]
    simp

/-- Scalar linear transformations commute with all linear transformations. -/
theorem scalarSubgroup_le_center : scalarSubgroup F V Q ≤ Subgroup.center (Omega F V Q) := by
  rintro g ⟨c,hc⟩
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change h.val.val (g.val.val v) = g.val.val (h.val.val v)
  rw [hc, hc, map_smul]

instance scalarSubgroup_normal : (scalarSubgroup F V Q).Normal where
  conj_mem := by
    intro g hg h
    have hc := (Subgroup.mem_center_iff.mp (scalarSubgroup_le_center F V Q hg) h)
    simpa [hc, mul_assoc] using hg

/-- The image of the orthogonal commutator group modulo scalar transformations. -/
abbrev ProjectiveOmega := Omega F V Q ⧸ scalarSubgroup F V Q

instance orthogonal_finite [Finite V] : Finite (Orthogonal F V Q) := by
  have : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V)) DFunLike.coe_injective
  infer_instance

instance projectiveOmega_finite [Finite V] : Finite (ProjectiveOmega F V Q) := inferInstance

/-- The projective map kills exactly the scalar transformations. -/
theorem projectiveOmega_mk_eq_one_iff (g : Omega F V Q) :
    QuotientGroup.mk' (scalarSubgroup F V Q) g = 1 ↔
      ∃ c : Fˣ, ∀ v : V, g.val.val v = (c : F) • v :=
  QuotientGroup.eq_one_iff g

end ClassicalOrthogonal.Minus
