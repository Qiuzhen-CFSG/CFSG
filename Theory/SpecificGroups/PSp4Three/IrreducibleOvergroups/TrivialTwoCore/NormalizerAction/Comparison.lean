module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.TrivialTwoCore.NormalizerAction.TenPoint
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.TrivialTwoCore.NormalizerAction.Commuting
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360

/-!
# Comparing the quadratic normalizer with the six-point symmetric action

The commuting part acts through the actual `PSL₂(9)`–`A₆` comparison; quadratic
conjugation acts as `(4 5)`. Thus the entire ten-point image belongs to the
faithful complementary-triple image of `S₆`. An anticommuting element cannot be
in the kernel, because its six-point permutation is odd. The commuting kernel
is scalar by the central-quotient definition of `PSL₂`, and those scalars are
exactly `±1`. This identifies the kernel with the ambient symplectic center.

The exceptional comparison is the ATLAS port `Order360`, attributed to Gerald
Höhn and the ATLAS contributors, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
ATLAS Research and Attribution License 1.0 (`LICENSES/ATLAS.txt`). The proof uses
its ten-point coherence theorem, not abstract recognition by order.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4/482 of `refs/quasithin.pdf`.
-/

@[expose] public section

noncomputable section
open Matrix
open scoped MatrixGroups LinearAlgebra.Projectivization
namespace Matrix.PSp4Three.TrivialTwoCore.NormalizerAction
open Atlas.Comparisons.Exceptional

theorem symmetricAction_injective : Function.Injective TriplePartitions.symmetricAction := by
  apply TriplePartitions.symmetricAction.ker_eq_bot_iff.mp
  by_contra h
  have hn := TriplePartitions.symmetricAction.ker.nontrivial_iff_ne_bot.mpr h
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 6)) hn
  have he : TriplePartitions.action TriplePartitions.firstCycle = 1 :=
    hle TriplePartitions.firstCycle.property
  rw [TriplePartitions.action_firstCycle] at he
  have hh := congrArg (fun p : Equiv.Perm (Fin 10) => p 0) he
  exact (by decide : (1 : Fin 10) ≠ 0) hh

theorem nine_permutation_mem_symmetric_range (a : PSL(2, Nine.F)) :
    Nine.permutation a ∈ TriplePartitions.symmetricAction.range :=
  ⟨(psl2NineCoordinatesEquivAlt6 a).val, psl2NineCoordinatesEquivAlt6_action a⟩

theorem tenPointAction_mem_symmetric_range (g : quadraticNormalizer) :
    tenPointAction g ∈ TriplePartitions.symmetricAction.range := by
  rcases (mem_quadraticNormalizer_iff g.val).mp g.property with hg | hg
  · obtain ⟨A, hA⟩ := exists_commuting_matrix g.val hg
    rw [tenPointAction_eq_of_matrix g A hA]
    exact nine_permutation_mem_symmetric_range _
  · have hc := anticommutes_mul_conjugation_commutes g.val hg
    obtain ⟨A, hA⟩ := exists_commuting_matrix (g * conjugationElement).val hc
    have hprod : tenPointAction (g * conjugationElement) ∈ TriplePartitions.symmetricAction.range := by
      rw [tenPointAction_eq_of_matrix _ A hA]
      exact nine_permutation_mem_symmetric_range _
    have hc' : tenPointAction conjugationElement ∈ TriplePartitions.symmetricAction.range :=
      ⟨Equiv.swap (4 : Fin 6) 5, symmetricAction_swap.trans tenPointAction_conjugation.symm⟩
    have he : tenPointAction (g * conjugationElement) * tenPointAction conjugationElement =
        tenPointAction g := by
      rw [← map_mul, mul_assoc, conjugationElement_sq, mul_one]
    rw [← he]
    exact TriplePartitions.symmetricAction.range.mul_mem hprod hc'

private theorem commuting_kernel_central (g : quadraticNormalizer)
    (hg : ∀ x : V, g.val • quadraticOperator x = quadraticOperator (g.val • x))
    (h : tenPointAction g = 1) : g.val ∈ Subgroup.center (Sp 2 (ZMod 3)) := by
  obtain ⟨A, hA⟩ := exists_commuting_matrix g.val hg
  have hproj : (A : PSL(2, Nine.F)) = 1 := Nine.permutation_injective (by
    rw [← tenPointAction_eq_of_matrix g A hA, h, map_one])
  have hcenter : A ∈ Subgroup.center (SL(2, Nine.F)) := (QuotientGroup.eq_one_iff A).mp hproj
  obtain ⟨a, ha, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
  have hs : a = 1 ∨ a = -1 := sq_eq_one_iff.mp (by simpa using ha)
  rcases hs with rfl | rfl
  · apply scalar_is_central g.val (1 : ZMod 3)
    intro x
    apply coordinates.injective
    have hx := hA (coordinates x)
    rw [← hscalar] at hx
    simpa [Matrix.scalar_apply, Matrix.diagonal_const_mulVec] using hx
  · apply scalar_is_central g.val (-1 : ZMod 3)
    intro x
    apply coordinates.injective
    have hx := hA (coordinates x)
    rw [← hscalar] at hx
    simpa [Matrix.scalar_apply, Matrix.diagonal_const_mulVec] using hx

/-- No anticommuting element acts trivially: its comparison permutation is odd. -/
private theorem anticommuting_not_kernel (g : quadraticNormalizer)
    (hg : ∀ x : V, g.val • quadraticOperator x = -quadraticOperator (g.val • x)) :
    tenPointAction g ≠ 1 := by
  intro h
  have hc := anticommutes_mul_conjugation_commutes g.val hg
  obtain ⟨A, hA⟩ := exists_commuting_matrix (g * conjugationElement).val hc
  have he : Nine.permutation (A : PSL(2, Nine.F)) = conjugationPermutation := by
    rw [← tenPointAction_eq_of_matrix _ A hA, map_mul, h, one_mul, tenPointAction_conjugation]
  have hs : (psl2NineCoordinatesEquivAlt6 (A : PSL(2, Nine.F))).val = Equiv.swap (4 : Fin 6) 5 :=
    symmetricAction_injective ((psl2NineCoordinatesEquivAlt6_action _).trans
      (he.trans symmetricAction_swap.symm))
  have hm := (psl2NineCoordinatesEquivAlt6 (A : PSL(2, Nine.F))).property
  rw [hs] at hm
  exact (by decide : Equiv.Perm.sign (Equiv.swap (4 : Fin 6) 5) ≠ 1)
    (Equiv.Perm.mem_alternatingGroup.mp hm)

/-- The projective-line kernel is exactly the actual ambient symplectic center. -/
theorem tenPointAction_eq_one_iff (g : quadraticNormalizer) :
    tenPointAction g = 1 ↔ g.val ∈ Subgroup.center (Sp 2 (ZMod 3)) := by
  constructor
  · intro h
    rcases (mem_quadraticNormalizer_iff g.val).mp g.property with hg | hg
    · exact commuting_kernel_central g hg h
    · exact (anticommuting_not_kernel g hg h).elim
  · intro h
    obtain ⟨a, ha⟩ := central_is_scalar g.val h
    apply Equiv.ext
    intro i
    apply Nine.marking.injective
    rw [tenPointAction_marking]
    change lineMap g (Nine.point i) = Nine.point i
    simp only [Nine.point, lineMap_mk]
    apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
    refine ⟨⟨a, 0⟩, ?_⟩
    rw [transport_apply, ha, map_smul, coordinates.apply_symm_apply]
    simpa using scalar_decomposition (⟨a, 0⟩ : Nine.F) (Nine.pointVector i)

end Matrix.PSp4Three.TrivialTwoCore.NormalizerAction
