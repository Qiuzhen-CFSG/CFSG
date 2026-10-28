module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.Reduction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.FullDerivedAction
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import Theory.GroupTheory.CComponent.TwoComponent.Involution

/-!
# The B₂ deduction from the Tits root table

The two full binary Ree parabolics are extensions of two-groups by the
concrete solvable groups PSL₂(2) and Sz(2). Restricting the marked embedding
therefore makes each Tits root parabolic solvable, and this persists under
conjugation. A fixed subgroup contained in one of them has no two-components.

The actual full binary Ree action on the Tits derived carrier is proved
bijective. Thus the only remaining inputs are the exhaustive binary involution
coverage and the two representative root-parabolic containments from
`InvolutionRootGeometry/Reduction`. This conditional theorem discharges
parabolic solvability and the full automorphism-action premise; it does not
assert the two outstanding finite-group calculations.

Sources: GLS II Definition 2.4; GLS III Theorem 2.5.15; Aschbacher–Smith
16.1.4, printed p.1171, and the binary parabolic calculation in F.1.12,
printed pp.263–264. The parabolics retain their literal derived intersections.
-/

public section

open Subgroup
namespace Tits.InvolutionRootGeometry
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds BenderSuzuki.MatrixGroups

theorem binary_seed_solvable (s : Side) : Group.IsSolvable (seed 0 s) := by
  let : Group.IsNilpotent (pCore 2 (seed 0 s)) := pCore_isNilpotent
  apply (Group.isSolvable_iff_subgroup_quotient (pCore 2 (seed 0 s))).mpr
  refine ⟨inferInstance, ?_⟩
  cases s with
  | linear =>
    let : Group.IsSolvable (LinearQuotient 0) :=
      Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by simpa using field_card 0)
    exact Group.isSolvable_of_isSolvable_injective
      (f := Binary.linearCoreQuotientEquiv.toMonoidHom) Binary.linearCoreQuotientEquiv.injective
  | suzuki =>
    let : Group.IsSolvable (SuzukiMatrixGroup 0) := suzukiZero_isSolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := Binary.suzukiCoreQuotientEquiv.toMonoidHom) Binary.suzukiCoreQuotientEquiv.injective

theorem rootParabolic_solvable (s : Side) : Group.IsSolvable (rootParabolic s) := by
  let : Group.IsSolvable (Parabolics.parabolic 0 s) := by
    rw [parabolic_zero]
    exact binary_seed_solvable s
  exact Group.isSolvable_of_isSolvable_injective
    (f := embedding.subgroupComap (Parabolics.parabolic 0 s))
    (fun x y h => Subtype.ext (embedding_injective (congrArg Subtype.val h)))

theorem isRootParabolic_solvable (P : Subgroup ParrottGroup) (hP : IsRootParabolic P) :
    Group.IsSolvable P := by
  obtain ⟨s, g, rfl⟩ := hP
  let : Group.IsSolvable (rootParabolic s) := rootParabolic_solvable s
  exact Group.isSolvable_of_surjective
    ((MulAut.conj g).toMonoidHom.subgroupMap_surjective (rootParabolic s))

theorem hasInvolutoryB2_of_root_coverage
    (hcover : BinaryInvolutionCoverage)
    (hlong : ∃ P : Subgroup ParrottGroup, IsRootParabolic P ∧ P < ⊤ ∧
      centralizer {parrottGenerator .s1} ≤ P)
    (hshort : ∃ P : Subgroup ParrottGroup, IsRootParabolic P ∧ P < ⊤ ∧
      centralizer {parrottGenerator .s4} ≤ P) :
    Theory.GroupTheory.HasInvolutoryB2 ParrottGroup := by
  apply Theory.GroupTheory.HasInvolutoryB2.of_fixed_solvable
  intro a ha
  obtain ⟨_, P, _, _, hP, _, hle, _⟩ := involution_table_of_representatives
    (OuterLocal.binaryDerivedAction_bijective derivedEquiv.symm) hcover hlong hshort a
    (by simpa only [ha] using pow_orderOf_eq_one a)
    (by intro h; simp [h] at ha)
  let : Group.IsSolvable P := isRootParabolic_solvable P hP
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

end Tits.InvolutionRootGeometry
