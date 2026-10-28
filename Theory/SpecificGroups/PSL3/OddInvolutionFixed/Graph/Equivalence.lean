module
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph
import all Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph

/-!
# The full orthogonal fixed group of a PSL₃ graph involution

The inverse Gram equation defining a determinant-one isometry rearranges to
exact fixation by the lifted graph actor. Thus the previously constructed
fixed-group embedding is surjective. The unique fixed lift through the
scalar center identifies the entire projective fixed group with this
orthogonal group, preserving the ambient group for component arguments.
Odd-prime automorphism coverage then applies this equivalence to every outer
involution of the actual simple, nonsolvable PSL₃ model.

The internal import is an intentional continuation of `Graph`'s matrix proof;
it uses the existing fixed-map definitions without widening their public API.
Source: GLS3, §§2.7 and 4.3; Aschbacher--Smith, proof of 15.3.38, printed p.1137,
and Theorem C, printed p.33.
-/

open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable BenderSuzuki.MatrixGroups
namespace Matrix.PSL3.OddInvolutionFixed
variable {F : Type*} [Field F]
/-- Every determinant-one isometry is an exactly fixed special linear matrix. -/
public theorem graphLinearFixedToOrthogonal_surjective (g : GL (Fin 3) F)
    (hs : g.val.transpose = g.val) : Function.Surjective (graphLinearFixedToOrthogonal g hs) := by
  intro x
  obtain ⟨hx, hd⟩ := ((graphOrthogonalForm g hs).mem_specialSubgroup_iff x.val).mp x.property
  let y : SL(3,F) := (slEquivDetKernel F).symm ⟨x.val, hd⟩
  have hy : SpecialLinearGroup.toGL y = x.val := slEquivDetKernel_symm_toGL F _
  have he : (inverseTransposeGL x.val)⁻¹ * g⁻¹ * x.val = g⁻¹ := by
    apply Units.ext
    exact hx
  have he' : g * inverseTransposeGL x.val * g⁻¹ = x.val := by
    calc
      _ = g * inverseTransposeGL x.val *
          ((inverseTransposeGL x.val)⁻¹ * g⁻¹ * x.val) := by rw [he]
      _ = x.val := by group
  have hf : y ∈ (linearConjSL F g * graphSL F).fixedSubgroup := by
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply SpecialLinearGroup.toGL_injective
    change SpecialLinearGroup.toGL (linearConjSL F g (graphSL F y)) = _
    rw [linearConjSL_toGL, graphSL_toGL, hy]
    exact he'
  refine ⟨⟨y, hf⟩, Subtype.ext ?_⟩
  exact hy

/-- The projective fixed-point embedding covers the whole orthogonal group. -/
public theorem graphFixedToOrthogonal_surjective (g : GL (Fin 3) F)
    (hg : (linearConj F g * graph F) ^ 2 = 1) :
    Function.Surjective (graphFixedToOrthogonal g hg) :=
  (graphLinearFixedToOrthogonal_surjective g (graph_involution_symmetric g hg)).comp
    (graphProjectiveFixedEquiv g).surjective

/-- A genuine equivalence of the full projective and orthogonal fixed groups. -/
public noncomputable def graphFixedOrthogonalEquiv (g : GL (Fin 3) F)
    (hg : (linearConj F g * graph F) ^ 2 = 1) :
    (linearConj F g * graph F).fixedSubgroup ≃*
      (graphOrthogonalForm g (graph_involution_symmetric g hg)).specialSubgroup :=
  MulEquiv.ofBijective (graphFixedToOrthogonal g hg)
    ⟨graphFixedToOrthogonal_injective g hg, graphFixedToOrthogonal_surjective g hg⟩

/-- Every outer involution over an odd prime field has a full orthogonal fixed group. -/
public theorem outer_fixed_equiv_orthogonal [Finite F] [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (a : MulAut PSL(3,F)) (ha : a ^ 2 = 1) (hout : ¬ ∃ k, a = MulAut.conj k) :
    ∃ J : HermitianForm 3 F, J.conj = 1 ∧ Nonempty (a.fixedSubgroup ≃* J.specialSubgroup) := by
  obtain ⟨g, rfl | rfl⟩ := automorphism_normal_form hns hp ho hF a
  · obtain ⟨k, hk⟩ := linearConj_involution_inner g ha
    exact (hout ⟨k, hk.symm⟩).elim
  · exact ⟨graphOrthogonalForm g (graph_involution_symmetric g ha), rfl,
      ⟨graphFixedOrthogonalEquiv g ha⟩⟩
end Matrix.PSL3.OddInvolutionFixed
