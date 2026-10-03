module

public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry
public import Theory.SpecificGroups.Suzuki.BorelSolvable

/-!
# Restricted Suzuki ovoid actions

An invariant subset of the Suzuki ovoid inherits the bound of two fixed
points for each nonidentity element. If it has at least three points, the
restricted subgroup action is faithful. Its point stabilizers are solvable,
since they embed into conjugates of the ambient Borel subgroup.

These facts apply to subgroup orbits without asserting that those orbits
are doubly transitive. They supply the elementary action transfers for the
subgroup argument of Huppert--Blackburn, *Finite Groups III*, XI.3.12(e),
printed p. 194, and the recognition theorem XI.11.15.
-/

namespace BenderSuzuki.MatrixGroups

/-- Every point stabilizer in the natural ovoid action is solvable. -/
public theorem suzukiOvoid_stabilizer_isSolvable
    {m : ℕ} (hm : 0 < m) (a : SuzukiOvoid m) :
    Group.IsSolvable (MulAction.stabilizer (SuzukiMatrixGroup m) a) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m)
    (suzukiOvoidInfinity m) a
  have hB : Group.IsSolvable
      (MulAction.stabilizer (SuzukiMatrixGroup m) (suzukiOvoidInfinity m)) := by
    rw [← suzukiBorelSubgroup_eq_stabilizer m hm]
    exact suzukiBorelSubgroup_isSolvable m hm
  let := hB
  let e := MulAction.stabilizerEquivStabilizer hg.symm
  exact Group.isSolvable_of_isSolvable_injective
    (f := e.symm.toMonoidHom) e.symm.injective

/-- Restricting to a subgroup preserves solvability of point stabilizers. -/
public theorem suzukiSubgroup_ovoid_stabilizer_isSolvable
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (a : SuzukiOvoid m) : Group.IsSolvable (MulAction.stabilizer H a) := by
  let := suzukiOvoid_stabilizer_isSolvable hm a
  let f : MulAction.stabilizer H a →*
      MulAction.stabilizer (SuzukiMatrixGroup m) a :=
    { toFun := fun g => ⟨g.val.val, g.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h))

/-- Point stabilizers remain solvable on any invariant ovoid subset. -/
public theorem suzukiSubaction_stabilizer_isSolvable
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (X : SubMulAction H (SuzukiOvoid m)) (a : X) :
    Group.IsSolvable (MulAction.stabilizer H a) := by
  let := suzukiSubgroup_ovoid_stabilizer_isSolvable hm H a.val
  let f : MulAction.stabilizer H a →* MulAction.stabilizer H a.val :=
    { toFun := fun g => ⟨g.val, congrArg Subtype.val g.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  intro x y h
  exact Subtype.ext (congrArg (fun z => z.val) h)

/-- No nonidentity subgroup element fixes three distinct points of an
invariant ovoid subset. -/
public theorem suzukiSubaction_at_most_two_fixed
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (X : SubMulAction H (SuzukiOvoid m))
    (g : H) (hg : g ≠ 1) (a b c : X)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (g • a = a ∧ g • b = b ∧ g • c = c) := by
  rintro ⟨ha, hb, hc⟩
  exact suzukiOvoid_at_most_two_fixed m hm g.val
    (fun h => hg (Subtype.ext h)) a.val b.val c.val
    (fun h => hab (Subtype.ext h)) (fun h => hac (Subtype.ext h))
    (fun h => hbc (Subtype.ext h))
    (congrArg Subtype.val ha) (congrArg Subtype.val hb) (congrArg Subtype.val hc)

/-- An invariant ovoid subset with at least three points is a faithful
subgroup action. No transitivity hypothesis is needed. -/
public theorem suzukiSubaction_faithful_of_two_lt_card
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (X : SubMulAction H (SuzukiOvoid m)) (hX : 2 < Nat.card X) :
    FaithfulSMul H X := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    Fintype.two_lt_card_iff.mp (show 2 < Fintype.card X by simpa using hX)
  refine ⟨fun {g h} heq => ?_⟩
  have hfix (x : X) : (g⁻¹ * h) • x = x := by
    rw [mul_smul, ← heq, inv_smul_smul]
  have hone : g⁻¹ * h = 1 := by
    by_contra hne
    exact suzukiSubaction_at_most_two_fixed hm H X (g⁻¹ * h) hne
      a b c hab hac hbc ⟨hfix a, hfix b, hfix c⟩
  exact inv_mul_eq_one.mp hone

/-- A nonempty invariant ovoid subset of size at most two forces the
subgroup to be solvable. The permutation image is abelian and its kernel
lies in a solvable point stabilizer. -/
public theorem suzukiSubaction_isSolvable_of_card_le_two
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (X : SubMulAction H (SuzukiOvoid m)) [Nonempty X]
    (hX : Nat.card X ≤ 2) : Group.IsSolvable H := by
  let a : X := Classical.choice inferInstance
  let := suzukiSubaction_stabilizer_isSolvable hm H X a
  let : IsMulCommutative (Equiv.Perm X) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr hX
  let : Group.IsSolvable (Equiv.Perm X) :=
    Group.isSolvable_of_comm (fun _ _ => mul_comm' _ _)
  apply Group.isSolvable_of_ker_le_range (MulAction.stabilizer H a).subtype
    (MulAction.toPermHom H X)
  rw [Subgroup.range_subtype]
  intro g hg
  exact congrArg (fun p : Equiv.Perm X => p a) hg

/-- Every nonempty invariant ovoid subset of a nonsolvable subgroup has
at least three points. -/
public theorem suzukiSubaction_two_lt_card_of_not_isSolvable
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H)
    (X : SubMulAction H (SuzukiOvoid m)) [Nonempty X] :
    2 < Nat.card X := by
  by_contra hX
  exact hH (suzukiSubaction_isSolvable_of_card_le_two hm H X (by omega))

/-- A nonsolvable subgroup acts faithfully on every nonempty invariant
ovoid subset, in particular on each of its orbits. -/
public theorem suzukiSubaction_faithful_of_not_isSolvable
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H)
    (X : SubMulAction H (SuzukiOvoid m)) [Nonempty X] :
    FaithfulSMul H X :=
  suzukiSubaction_faithful_of_two_lt_card hm H X
    (suzukiSubaction_two_lt_card_of_not_isSolvable hm H hH X)

end BenderSuzuki.MatrixGroups
