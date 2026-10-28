module

public import Theory.AtlasPort.LinearGroups.G2.FieldTransport
public import Theory.Representation.AbsolutelyIrreducible
public import Theory.Representation.SemilinearConjugation

/-!
# The one-dimensional restricted factor of G₂

The base field with the trivial action is absolutely irreducible: its scalar
endomorphisms already exhaust its full endomorphism algebra. This constructs the
weight-zero factor in GLS3, Example 2.8.10(g).
-/

@[expose] public section

namespace Atlas.G2.Restricted.Trivial

variable (F : Type*) [Field F]

/-- The actual one-dimensional trivial G₂ module. -/
abbrev Space := F

/-- Every element of the actual group acts as the identity. -/
def action : Representation F (Model F) (Space F) := 1

@[simp] theorem action_apply (g : Model F) (v : Space F) : action F g v = v := rfl

@[simp] theorem finrank_space : Module.finrank F (Space F) = 1 := Module.finrank_self F

/-- Scalar endomorphisms exhaust the algebra of endomorphisms of a line. -/
theorem adjoin_action_eq_top : Algebra.adjoin F (Set.range (action F)) = ⊤ := by
  apply top_unique
  intro f _
  have hf : f = algebraMap F (Module.End F F) (f 1) := by
    apply LinearMap.ext
    intro x
    have hx := f.map_smul x (1 : F)
    simpa [Algebra.algebraMap_eq_smul_one, mul_comm] using hx
  rw [hf]
  exact Subalgebra.algebraMap_mem _ _

/-- The trivial factor stays irreducible under arbitrary scalar extension. -/
theorem absolutelyIrreducible : Representation.IsAbsolutelyIrreducible (action F) := by
  constructor
  apply Representation.irreducible_of_jacobson_density_surjective
  exact (Representation.extendScalars_surj_iff (AlgebraicClosure F) (action F)).mp
    (adjoin_action_eq_top F)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The field automorphism on the trivial line, as a semilinear equivalence. -/
def coefficientEquiv (e : F ≃+* F) :
    LinearEquiv (e : F →+* F) (σ' := (e.symm : F →+* F)) (Space F) (Space F) where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := e.map_add
  map_smul' a b := e.map_mul a b

/-- Coefficient conjugation agrees with twisting the actual group. -/
theorem coefficientConjugate_eq (e : F ≃+* F) :
    Representation.semilinearConjugate e (action F) (coefficientEquiv F e) =
      (action F).comp (fieldEquiv e).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  rw [Representation.semilinearConjugate_apply]
  change e (e.symm v) = v
  exact e.apply_symm_apply v

end Atlas.G2.Restricted.Trivial
