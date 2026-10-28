module

public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates
public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The invariant polar form on the natural G₂ quotient

In characteristic two, the scalar identity is the radical of the norm polar
form on trace-zero octonions. Choosing the representative with both scalar
coordinates zero therefore gives a well-defined form on the natural quotient.
Pairing the six opposite coordinates proves nondegeneracy. Preservation of the
octonion norm proves invariance under the actual full automorphism group.

This supplies the duality used for the J₂ restriction in Aschbacher--Smith,
K.4.5, printed p.460. Octonion conventions and the ATLAS attribution and license
are retained in the imported `NormGeometry` and `NaturalCoordinates` modules.
-/

@[expose] public noncomputable section
namespace Atlas.G2.Natural.InvariantPolar
open Atlas.G2.Restricted.NaturalCoordinates
open Atlas.SplitOctonion
variable (F : Type*) [Field F] [CharP F 2]

def form : LinearMap.BilinForm F (Natural.Space F) :=
  let r := (Natural.TraceZero F).subtype.comp ((representative F).comp (coordinates F))
  normPolar.compl₁₂ r r

theorem form_mk (x y : Natural.TraceZero F) :
    form F (Natural.mk F x) (Natural.mk F y) = normPolar x.val y.val := by
  have hx : x.val 4 = x.val 3 := by
    have h : x.val 3 + x.val 4 = 0 := x.property
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right h
  have hy : y.val 4 = y.val 3 := by
    have h : y.val 3 + y.val 4 = 0 := y.property
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right h
  simp [form, normPolar, representative, projection, hx, hy,
    CharTwo.add_self_eq_zero, add_assoc]

theorem form_invariant (g : Model F) (x y : Natural.Space F) :
    form F (Natural.action F g x) (Natural.action F g y) = form F x y := by
  obtain ⟨x, rfl⟩ := Natural.mk_surjective F x
  obtain ⟨y, rfl⟩ := Natural.mk_surjective F y
  rw [Natural.action_mk, Natural.action_mk, form_mk, form_mk]
  exact automorphism_normPolar g x.val y.val

private theorem separating (x : Natural.Space F)
    (hx : ∀ y, form F x y = 0) : x = 0 := by
  apply (equiv F).injective
  change coordinates F x = coordinates F 0
  rw [map_zero]
  ext i
  have hi := hx (quotientClass F (Pi.single (5 - i) 1))
  fin_cases i <;>
    simpa [form, normPolar, representative, Pi.single_apply] using hi

theorem form_symm (x y : Natural.Space F) : form F x y = form F y x :=
  normPolar_symm _ _

/-- The polar form is alternating in characteristic two. -/
theorem form_alternating : (form F).IsAlt := by
  intro x
  change normPolar _ _ = 0
  rw [normPolar_self]
  simp [CharTwo.two_eq_zero]

/-- The six opposite coordinate pairs detect every quotient vector. -/
theorem form_nondegenerate : (form F).Nondegenerate := by
  constructor
  · exact separating F
  · intro y hy
    apply separating F y
    intro x
    rw [form_symm]
    exact hy x

end Atlas.G2.Natural.InvariantPolar
