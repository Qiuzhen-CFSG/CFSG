module

public import Stellmacher.MainDefs
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The two-group vocabulary for ABG fusion

Chapter I (article p.2) gives the wreathed presentation of order 2^(2n+1),
n ≥ 2. Chapter II §2 Definition 2 assigns height n to these groups and height
one to quasi-dihedral groups. The quasi-dihedral predicate is the existing
semidihedral presentation, whose order exponent differs by one from the paper.

The remaining predicates name the concrete four, quaternion and generalized
quaternion groups used in Chapter II §1 Lemmas 1–3 and its fusion propositions.
Generalized quaternion includes order eight. These are structural definitions,
not assertions of the local classification or fusion theorems. The exact
presentation equations and model equivalences are intentionally exposed so
subsequent proof modules can construct and transport their witnesses.
-/

noncomputable section

namespace ABG

universe u

/-- The wreathed presentation of article p.2, including its prescribed order. -/
@[expose] public def IsWreathedOfHeight (G : Type u) [Group G] (n : ℕ) : Prop :=
  2 ≤ n ∧ Nat.card G = 2 ^ (2 * n + 1) ∧
    ∃ s t z : G, s ^ (2 ^ n) = 1 ∧ t ^ (2 ^ n) = 1 ∧ z ^ 2 = 1 ∧
      z⁻¹ * s * z = t ∧ z⁻¹ * t * z = s ∧ s * t = t * s ∧
      Subgroup.closure ({s, t, z} : Set G) = ⊤

/-- Wreathed means height at least two, as required in Chapter I. -/
@[expose] public def IsWreathedGroup (G : Type u) [Group G] : Prop :=
  ∃ n : ℕ, IsWreathedOfHeight G n

/-- Chapter II Definition 2: quasi-dihedral groups have height one. -/
@[expose] public def HasTwoGroupHeight (S : Type u) [Group S] (n : ℕ) : Prop :=
  (n = 1 ∧ Stellmacher.IsSemidihedralGroup S) ∨ IsWreathedOfHeight S n

/-- Height of a finite group is the height of its Sylow two subgroup. -/
@[expose] public def HasHeight (G : Type u) [Group G] (n : ℕ) : Prop :=
  ∃ S : Sylow 2 G, HasTwoGroupHeight S n

/-- Generalized quaternion two-groups, including the quaternion group of order eight. -/
@[expose] public def IsGeneralizedQuaternionGroup (G : Type u) [Group G] : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃* QuaternionGroup (2 ^ n))

/-- A four group is the elementary abelian group of order four. -/
public abbrev IsFourGroup (G : Type u) [Group G] : Prop :=
  IsKleinFour G

/-- The ordinary quaternion group, of order eight. -/
@[expose] public def IsQuaternionGroup (G : Type u) [Group G] : Prop :=
  Nonempty (G ≃* QuaternionGroup 2)

/-- Having generalized quaternion Sylow two-subgroups. -/
@[expose] public def HasGeneralizedQuaternionSylowTwo (G : Type u) [Group G] : Prop :=
  ∃ S : Sylow 2 G, IsGeneralizedQuaternionGroup S

/-- Having dihedral Sylow two-subgroups. -/
@[expose] public def HasDihedralSylowTwo (G : Type u) [Group G] : Prop :=
  ∃ S : Sylow 2 G, Stellmacher.IsDihedralGroup S

end ABG
