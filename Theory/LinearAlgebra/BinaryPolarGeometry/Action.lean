module

public import Theory.LinearAlgebra.BinaryPolarGeometry
public import Theory.Representation.BinaryPermutation
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The original action on a reconstructed binary polar space

Permutation of the original points permutes their non-incidence rows. Thus
the row span is an invariant subspace of the literal permutation module.
Faithfulness on points implies faithfulness on this subspace, and the form
constructed by evaluation is invariant. The point stabilizers are unchanged.

Source: Aschbacher–Smith I.5.15, printed p.424.
-/

@[expose] public noncomputable section
namespace Theory.LinearAlgebra.BinaryPolarGeometry
namespace Data
variable {G X : Type*} [Group G] [MulAction G X]
variable {R : X → X → Prop} (d : Data R)
variable (hR : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)

def permutationRepresentation : Representation (ZMod 2) G (X → ZMod 2) :=
  (BinaryPermutation.representation X).comp (MulAction.toPermHom G X)

include hR in
theorem row_action (g : G) (x : X) :
    permutationRepresentation g (row R x) = row R (g • x) := by
  classical
  ext y
  change (if R x (g⁻¹ • y) then 0 else 1) = if R (g • x) y then 0 else 1
  have hi := hR g x (g⁻¹ • y)
  simp only [smul_inv_smul] at hi
  simp only [hi]

def rowSubrepresentation : Subrepresentation (permutationRepresentation (G := G) (X := X)) where
  toSubmodule := rowSpan R
  apply_mem_toSubmodule g v hv := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      rw [row_action hR]
      exact Submodule.subset_span ⟨g • x, rfl⟩
    | zero => simpa only [map_zero] using (rowSpan R).zero_mem
    | add v w _ _ hv hw => simpa only [map_add] using (rowSpan R).add_mem hv hw
    | smul a v _ hv => simpa only [map_smul] using (rowSpan R).smul_mem a hv

def representation : Representation (ZMod 2) G (Space R) :=
  (rowSubrepresentation hR).toRepresentation

theorem representation_point (g : G) (x : X) :
    representation hR g (point R x) = point R (g • x) :=
  Subtype.ext (row_action hR g x)

include d in
theorem representation_injective [FaithfulSMul G X] :
    Function.Injective (representation hR) := by
  intro g h he
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  apply d.point_injective
  rw [← representation_point hR, ← representation_point hR, he]

theorem form_invariant (g : G) (v w : Space R) :
    d.form (representation hR g v) (representation hR g w) = d.form v w := by
  obtain rfl | ⟨x, rfl⟩ :=
    BinaryPointMap.eq_zero_or_mem_range _ d.point_add (span_points (R := R)) v
  · simp only [map_zero, LinearMap.zero_apply]
  obtain rfl | ⟨y, rfl⟩ :=
    BinaryPointMap.eq_zero_or_mem_range _ d.point_add (span_points (R := R)) w
  · simp only [map_zero]
  rw [representation_point hR, representation_point hR, d.form_points, d.form_points]
  unfold row
  rw [hR]

include d in
theorem fixes_point_iff (g : G) (x : X) :
    representation hR g (point R x) = point R x ↔ g • x = x := by
  rw [representation_point hR]
  exact d.point_injective.eq_iff

end Data
end Theory.LinearAlgebra.BinaryPolarGeometry
