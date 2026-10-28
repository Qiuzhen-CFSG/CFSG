module
public import Theory.Representation.BinaryPermutation.EightGeometry
public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation
public import Theory.LinearAlgebra.BinaryHyperplaneSpan

/-!
# Singular-point transport and perpendicular spanning in the six-space

Weight-four representatives and even permutation transitivity transport
any nonzero singular point to any other. Nondegeneracy of the original
half-weight polar form makes distinct points give distinct binary
functionals, whose perpendiculars span the whole natural section.

The actual constant-line quotient and form come from EightGeometry,
which preserves attribution to the ATLAS half-weight construction.
Source: Aschbacher--Smith, 12.6.24(3--5), printed pp.830--831.
-/

public section
namespace BinaryPermutation.EightGeometry
open TerminalOrthogonal.Eight

/-- The original alternating-eight action is transitive on nonzero singular vectors. -/
theorem singular_transitive (v w : natural (Fin 8)) (hv : v ≠ 0) (hw : w ≠ 0)
    (hqv : form v = 0) (hqw : form w = 0) :
    ∃ a : alternatingGroup (Fin 8), naturalRepresentation (Fin 8) a.val v = w := by
  obtain ⟨u,rfl,hu⟩ := (singular_iff_weight_four v hv).mp hqv
  obtain ⟨r,rfl,hr⟩ := (singular_iff_weight_four w hw).mp hqw
  obtain ⟨a,ha⟩ := exists_even_permutation_of_weight
    (by decide : 3 ≤ Fintype.card (Fin 8)) u.val r.val (hu.trans hr.symm)
  refine ⟨a,?_⟩
  rw [←coreToNatural_equivariant]
  exact congrArg (coreToNatural (Fin 8)) (Subtype.ext ha)

/-- Distinct point perpendiculars generate the full six-dimensional section. -/
theorem perpendicular_sup (v w : natural (Fin 8)) (hne : v ≠ w) :
    (form.polarBilin v).ker ⊔ (form.polarBilin w).ker = ⊤ := by
  apply LinearMap.binary_ker_sup_eq_top_of_ne
  intro he
  apply hne
  apply sub_eq_zero.mp
  apply polar_nondegenerate.1
  intro x
  simp only [map_sub,he,sub_self,LinearMap.zero_apply]
end BinaryPermutation.EightGeometry
