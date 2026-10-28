module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.Reduction
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.UniversalKernel
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.KernelGeneration

/-!
# The marked diagonal action and the universal covering kernel

The actual projective-action map pulls the inner automorphism subgroup back
to L. Thus the selected diagonal projects to a non-inner cubic element of
the standard projective automorphism group. Generation of the universal
kernel by squares and displacements for this element forces it to move the
covering center, by the universal-cover transfer. The marked field inversion
then supplies the full action on the central four-group.

The concrete exceptional-cover calculation discharges kernel generation for
the marked diagonal element. The resulting movement and full center action
require only the original overgroup and normalizer geometry. The conditional
transfer lemmas remain available. The original diagonal element, cover, and
projective quotient are retained throughout.
Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004.
-/

public section

open Subgroup PerfectCentralCovering
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

private theorem projectiveAction_on_linear (c : FourCover L) (l : L) :
    projectiveAction L c (l : I) = MulAut.conj (c.toMonoidHom l) := by
  ext y
  obtain ⟨x, rfl⟩ := c.surjective y
  change c.toCover.autMap c.ker_eq_center (MulAut.conjNormal (l : I))
    (c.toMonoidHom x) = _
  rw [c.toCover.autMap_apply, MulAut.conjNormal_val]
  change c.toMonoidHom (l * x * l⁻¹) = _
  simp only [map_mul, map_inv, MulAut.conj_apply]

/-- The inner projective subgroup has precisely the original linear preimage. -/
theorem projectiveAction_mem_inner_iff (d : Overgroup L) (x : I) :
    projectiveAction L d.cover x ∈ MulAut.innerSubgroup PSL ↔ x ∈ L := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨l, rfl⟩ := d.cover.surjective y
    have he : projectiveAction L d.cover (l : I) = projectiveAction L d.cover x :=
      (projectiveAction_on_linear d.cover l).trans hy
    have hk : x * (l : I)⁻¹ ∈ (projectiveAction L d.cover).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    rw [d.projectiveAction_ker] at hk
    have hL := L.mul_mem (map_subtype_le (center L) hk) l.property
    simpa only [inv_mul_cancel_right] using hL
  · intro hx
    exact ⟨d.cover.toMonoidHom ⟨x, hx⟩, (projectiveAction_on_linear d.cover ⟨x, hx⟩).symm⟩

/-- The marking gives a genuine outer cubic element of the standard projective group. -/
theorem diagonal_projective_properties (d : Overgroup L) (n : NormalizerGeometry d) :
    projectiveAction L d.cover n.diagonalElement ∈ PSL3.OuterSolvable.standard F ∧
      (projectiveAction L d.cover n.diagonalElement) ^ 3 = 1 ∧
      projectiveAction L d.cover n.diagonalElement ∉ MulAut.innerSubgroup PSL := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← d.full_action]
    exact ⟨n.diagonalElement, rfl⟩
  · rw [← map_pow, n.diagonalElement_cube, map_one]
  · exact fun hi => n.diagonalElement_notMem_linear ((projectiveAction_mem_inner_iff d _).mp hi)

/-- The universal-kernel calculation transfers to the original marked diagonal element. -/
theorem diagonal_moves_center_of_kernel_generation (d : Overgroup L)
    (n : NormalizerGeometry d)
    (hgen : (universalProjection PSL).ker ≤
      kernelSquaresAndDisplacements (projectiveAction L d.cover n.diagonalElement)) :
    n.diagonalElement ∉ centralizer ((center L).map L.subtype : Set I) := by
  obtain ⟨z, hz⟩ := cover_moves_center_of_kernel_generation d.cover
    (MulAut.conjNormal n.diagonalElement) (projectiveAction L d.cover n.diagonalElement)
    (fun x => (d.cover.toCover.autMap_apply d.cover.ker_eq_center _ x).symm) hgen
  intro hc
  apply hz
  apply Subtype.ext
  change n.diagonalElement * ((z : L) : I) * n.diagonalElement⁻¹ = ((z : L) : I)
  rw [← hc z (mem_map_of_mem L.subtype z.property), mul_inv_cancel_right]

/-- The same kernel calculation supplies full center action through field inversion. -/
theorem centralFourAction_surjective_of_kernel_generation (d : Overgroup L)
    (n : NormalizerGeometry d)
    (hgen : (universalProjection PSL).ker ≤
      kernelSquaresAndDisplacements (projectiveAction L d.cover n.diagonalElement)) :
    Function.Surjective (centralFourAction d n.graphFieldI) :=
  centralFourAction_surjective_of_diagonal_moves d n
    (diagonal_moves_center_of_kernel_generation d n hgen)

/-- The marked diagonal element moves the actual covering center, as used in
15.3.38. The universal-kernel calculation supplies the movement without any
additional center-action, containment, or residual-model premise. -/
theorem diagonal_moves_center (d : Overgroup L) (n : NormalizerGeometry d) :
    n.diagonalElement ∉ centralizer ((center L).map L.subtype : Set I) := by
  obtain ⟨hstandard, hcube, houter⟩ := diagonal_projective_properties d n
  exact diagonal_moves_center_of_kernel_generation d n
    (kernel_generation (projectiveAction L d.cover n.diagonalElement)
      hstandard hcube houter)

/-- The chosen graph-field centralizer induces the full automorphism group
on the central four-group. The marked field inversion completes the action
once the diagonal movement has been established. -/
theorem centralFourAction_surjective (d : Overgroup L) (n : NormalizerGeometry d) :
    Function.Surjective (centralFourAction d n.graphFieldI) :=
  centralFourAction_surjective_of_diagonal_moves d n (diagonal_moves_center d n)

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
