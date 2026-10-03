module

public import Theory.SpecificGroups.Suzuki.SubgroupOvoid
public import Theory.SpecificGroups.Suzuki.SubgroupFrobenius
public import Theory.GroupAction.RegularNormal
public import BenderSuzuki.External.Huppert.XI.FrobeniusKernel
public import BenderSuzuki.External.Huppert.XI.SubgroupKernelNoncommutative

/-!
# Local recognition data for Suzuki subgroup actions

A nonsolvable Suzuki subgroup acting doubly transitively on a nonempty
invariant part of the ovoid has no nontrivial regular normal subgroup:
such a subgroup would be elementary abelian, and its solvable stabilizer
supplement would make the whole group solvable. The inherited fixed-point
bound then supplies Frobenius kernels in the point stabilizers. Their
containment in conjugate root groups makes them 2-groups, and the root
coordinates and pair-swapping geometry force them to be noncommutative.
These are the local inputs to the Suzuki recognition theorem XI.11.15.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.12(e) and XI.11.15.
-/

namespace BenderSuzuki.MatrixGroups

/-- A nonsolvable doubly transitive Suzuki subaction has no nontrivial
regular normal subgroup. -/
public theorem suzukiSubaction_no_regular_normal
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H)
    (X : SubMulAction H (SuzukiOvoid m)) [Nonempty X]
    (htwo : MulAction.IsMultiplyPretransitive H X 2) :
    ¬ ∃ R : Subgroup H, R.Normal ∧ R ≠ ⊥ ∧
      ∀ x y : X, ∃! r : R, (r : H) • x = y := by
  rintro ⟨R, hRnormal, hRne, hRregular⟩
  let a : X := Classical.choice inferInstance
  let := suzukiSubaction_stabilizer_isSolvable hm H X a
  exact hH (MulAction.isSolvable_of_regular_normal_of_isSolvable_stabilizer
    htwo a R hRnormal hRne hRregular)

set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Each pair of distinct points of a nonsolvable doubly transitive Suzuki
subaction determines a point-stabilizer Frobenius kernel. -/
public theorem suzukiSubaction_frobeniusKernel_exists
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H)
    (X : SubMulAction H (SuzukiOvoid m)) [Nonempty X]
    (htwo : MulAction.IsMultiplyPretransitive H X 2)
    (a b : X) (hab : a ≠ b) :
    ∃ F : Subgroup (MulAction.stabilizer H a),
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer H a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer H a)) := by
  let := suzukiSubaction_faithful_of_not_isSolvable hm H hH X
  exact External.huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
    htwo (suzukiSubaction_at_most_two_fixed hm H X)
    (suzukiSubaction_no_regular_normal hm H hH X htwo) a b hab

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- A base point in a nonsolvable doubly transitive Suzuki subaction admits
a second point and a point-stabilizer Frobenius kernel that is a 2-group. -/
public theorem suzukiSubaction_frobeniusTwoKernel_exists
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H)
    (X : SubMulAction H (SuzukiOvoid m)) [Nonempty X]
    (htwo : MulAction.IsMultiplyPretransitive H X 2) (a : X) :
    ∃ (b : X) (hab : a ≠ b) (F : Subgroup (MulAction.stabilizer H a)),
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer H a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer H a)) ∧
      IsPGroup 2 F := by
  have hcard := suzukiSubaction_two_lt_card_of_not_isSolvable hm H hH X
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b, hba⟩ := exists_ne a
  refine ⟨b, hba.symm, ?_⟩
  refine Exists.imp ?_ (suzukiSubaction_frobeniusKernel_exists hm H hH X htwo a b hba.symm)
  intro F hFrob
  exact ⟨hFrob, suzukiSubaction_frobeniusKernel_isPGroup hm H X a hFrob⟩

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The noncommutative Frobenius 2-kernel required by Suzuki recognition
exists at every base point of a nonsolvable doubly transitive subaction. -/
public theorem suzukiSubaction_noncommutativeFrobeniusTwoKernel_exists
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H)
    (X : SubMulAction H (SuzukiOvoid m)) [Nonempty X]
    (htwo : MulAction.IsMultiplyPretransitive H X 2) (a : X) :
    ∃ (b : X) (hab : a ≠ b) (F : Subgroup (MulAction.stabilizer H a)),
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer H a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer H a)) ∧
      ¬ IsMulCommutative F ∧ IsPGroup 2 F := by
  refine Exists.imp ?_ (suzukiSubaction_frobeniusTwoKernel_exists hm H hH X htwo a)
  intro b
  apply Exists.imp
  intro hab
  apply Exists.imp
  intro F hF
  exact ⟨hF.1,
    suzukiSubaction_frobeniusKernel_not_isMulCommutative hm H hH X htwo a b hab F hF.1,
    hF.2⟩

end BenderSuzuki.MatrixGroups
