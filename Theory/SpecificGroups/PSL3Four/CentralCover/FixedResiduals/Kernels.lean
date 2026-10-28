module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.Restriction
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.SylowModels
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Projection
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveField
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover

/-!
# Trivial kernels for the graph and field fixed residuals

Every involution in the kernel of the universal PSL₃(4) cover is a square
in that kernel, by the proved exceptional multiplier C₄ × C₄ × C₃. The
restriction theorem applies to the perfect residuals: their projective
images are PSL₂(4) and PSL₃(2), whose actual Sylow subgroups are constructed
in `SylowModels`. This proves injectivity of the field residual projection
unconditionally. The graph residual projection is injective with its
projective model retained as the independent input allowed by the assembly.

The existing conditional restriction interfaces are preserved; their
square-root premise is discharged using `ExceptionalFourCover.canonicalKernelEquiv`
on the literal canonical projection. No splitting assumption is used.
Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, and I.1.3(6),
printed p.407 (1 March 2004 manuscript).
-/

public section

open Subgroup PerfectCentralCovering
namespace Matrix.PSL3Four

/-- The precise exceptional multiplier input needed for the residual projections. -/
@[expose] def UniversalKernelInvolutionsAreSquares : Prop :=
  ∀ z ∈ (universalProjection PSL).ker, z ^ 2 = 1 →
    ∃ w ∈ (universalProjection PSL).ker, w ^ 2 = z

/-- An actual multiplier isomorphism supplies the needed square roots. -/
theorem universalKernelInvolutionsAreSquares_of_model
    (e : (universalProjection PSL).ker ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) × Multiplicative (ZMod 3)) :
    UniversalKernelInvolutionsAreSquares := by
  intro z hz hz2
  let x : (universalProjection PSL).ker := ⟨z, hz⟩
  have hx : (e x) ^ 2 = 1 := by
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext hz2, map_one]
  have hs : ∀ a : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ×
      Multiplicative (ZMod 3), a ^ 2 = 1 → ∃ b, b ^ 2 = a := by decide +kernel
  obtain ⟨y, hy⟩ := hs (e x) hx
  refine ⟨e.symm y, (e.symm y).property, ?_⟩
  have he : (e.symm y) ^ 2 = x := by
    apply e.injective
    simpa only [map_pow, e.apply_symm_apply] using hy
  exact congrArg Subtype.val he

/-- The proved exceptional multiplier makes every canonical kernel involution
a square in that same kernel. This discharges the multiplier input of 15.3.38. -/
theorem universalKernelInvolutionsAreSquares : UniversalKernelInvolutionsAreSquares :=
  universalKernelInvolutionsAreSquares_of_model PSL3.ExceptionalFourCover.canonicalKernelEquiv

variable {E : Type*} [Group E] [Finite E] {c : FourCover E}

private theorem fixedResidualMap_injective_of_kernel_squares
    (α : MulAut E) (β : MulAut PSL)
    (heq : ∀ x, c.toMonoidHom (α x) = β (c.toMonoidHom x))
    [Group.IsPerfect (pResidual 2 β.fixedSubgroup)]
    (hsquare : UniversalKernelInvolutionsAreSquares)
    (hdihedral : ∀ S : Sylow 2 (pResidual 2 β.fixedSubgroup),
      ∃ n : ℕ, 0 < n ∧ Nonempty (S ≃* DihedralGroup n)) :
    Function.Injective (MulAut.fixedResidualMap 2 α β c.toMonoidHom heq) := by
  let f := MulAut.fixedResidualMap 2 α β c.toMonoidHom heq
  have hf : Function.Surjective f := MulAut.fixedResidualMap_surjective 2 α β
    c.toMonoidHom c.surjective c.ker_le_center c.ker_isTwoGroup heq
  let : Group.IsPerfect (pResidual 2 α.fixedSubgroup) :=
    isPerfect_of_isPPerfect_of_surjective (Subgroup.isPPerfect_pResidual 2) f hf
      (MulAut.fixedResidualMap_ker_isPGroup 2 α β c.toMonoidHom heq c.ker_isTwoGroup)
  let : Group.IsPerfect PSL := Atlas.psl_perfect (F := F) 3 (by decide)
  let i : pResidual 2 α.fixedSubgroup →* E :=
    α.fixedSubgroup.subtype.comp (pResidual 2 α.fixedSubgroup).subtype
  let j : pResidual 2 β.fixedSubgroup →* PSL :=
    β.fixedSubgroup.subtype.comp (pResidual 2 β.fixedSubgroup).subtype
  have hc2 (z : E) (hz : z ∈ c.toMonoidHom.ker) : z ^ 2 = 1 := by
    let := c.center_isKleinFour
    let w : center E := ⟨z, c.ker_le_center hz⟩
    have hw := Monoid.pow_exponent_eq_one w
    rw [IsKleinFour.exponent_two] at hw
    exact congrArg Subtype.val hw
  apply injective_of_universal_kernel_involutions_are_squares c.toCover hc2 hsquare
    i (α.fixedSubgroup.subtype_injective.comp (pResidual 2 α.fixedSubgroup).subtype_injective)
    f hf j _ hdihedral
  rfl

/-- The graph projection is injective if the universal kernel has square roots
of its involutions. Its projective model is the separately supplied input. -/
theorem CoverActions.graphResidualProjection_injective_of_kernel_squares
    (a : CoverActions E c) (hsquare : UniversalKernelInvolutionsAreSquares)
    (e : pResidual 2 (PSL3.OuterSolvable.graph F).fixedSubgroup ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F) :
    Function.Injective a.graphResidualProjection := by
  let : Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by rw [card_F]; decide)
  let : Group.IsPerfect (pResidual 2 (PSL3.OuterSolvable.graph F).fixedSubgroup) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  apply fixedResidualMap_injective_of_kernel_squares a.graph _ a.graph_compatible hsquare
  intro S
  obtain ⟨d⟩ := FixedResidualKernels.psl2Four_sylow_dihedral
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  refine ⟨2, by decide, ⟨(e.subgroupMap
    (S : Subgroup (pResidual 2 (PSL3.OuterSolvable.graph F).fixedSubgroup))).trans ?_⟩⟩
  exact d

/-- The field projection is injective if the universal kernel has square roots
of its involutions; the binary projective model is supplied unconditionally. -/
theorem CoverActions.fieldResidualProjection_injective_of_kernel_squares
    (a : CoverActions E c) (hsquare : UniversalKernelInvolutionsAreSquares) :
    Function.Injective a.fieldResidualProjection := by
  let e := projectiveFieldResidualEquiv
  let : Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_perfect (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect (pResidual 2 pslFrobenius.fixedSubgroup) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  apply fixedResidualMap_injective_of_kernel_squares a.field _ a.field_compatible hsquare
  intro S
  obtain ⟨d⟩ := FixedResidualKernels.psl3Two_sylow_dihedral
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  refine ⟨4, by decide, ⟨(e.subgroupMap
    (S : Subgroup (pResidual 2 pslFrobenius.fixedSubgroup))).trans ?_⟩⟩
  exact d

/-- The graph residual projection has trivial kernel. Only the independent
projective graph model remains an input; the exceptional multiplier input
is discharged by its actual canonical kernel isomorphism. -/
theorem CoverActions.graphResidualProjection_injective_of_projective_model
    (a : CoverActions E c)
    (e : pResidual 2 (PSL3.OuterSolvable.graph F).fixedSubgroup ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F) :
    Function.Injective a.graphResidualProjection :=
  a.graphResidualProjection_injective_of_kernel_squares
    universalKernelInvolutionsAreSquares e

/-- The field residual projection has trivial kernel, using the proved binary
projective model and exceptional canonical kernel isomorphism. -/
theorem CoverActions.fieldResidualProjection_injective (a : CoverActions E c) :
    Function.Injective a.fieldResidualProjection :=
  a.fieldResidualProjection_injective_of_kernel_squares universalKernelInvolutionsAreSquares

end Matrix.PSL3Four
