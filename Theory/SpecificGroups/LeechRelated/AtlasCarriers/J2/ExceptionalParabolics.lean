module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Theory.GroupTheory.Amalgam.LocalStructure
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.QuaternionDihedralInvolutionCosets
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Marked Hall--Janko local models

This file retains legacy output contracts for cases F.1.12(I)(10)--(11).
They are not source-faithful model specifications: `MarkedParabolics` assumes
`S ≤ Lᵢ`, collapsing `L₁S` to `L₁` in the outer case, and the predicates
below existentially quantify over arbitrary ambient groups. The corrected,
carrier-indexed source boundary is the `HallJanko` namespace in
`CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko`.
The public names here are retained for compatibility.

The
ambient carrier in the first case is the published degree-100 permutation
carrier.  The second case uses its actual automorphism group, `MulAut Carrier`.

The local data are kept as a structure because the ATLAS carrier file proves
only the permutation carrier and its faithful inclusion.  In particular, it
does not prove the order of the generated group, simplicity, or the subgroup
calculations in the Hall--Janko parabolics.  A model witness therefore has to
provide those calculations explicitly.  This prevents an order-only carrier
from being silently used as `J₂`.

The two legacy predicates ask only for `RankTwoAmalgam.ParabolicEquiv`.
They impose no compatibility or uniqueness condition, but their missing
ambient-carrier identification prevents their use as source alternatives.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12(I)(10)--(11), printed p. 263 (PDF p. 274).
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2

open Theory.GroupTheory
open Matrix

/-- The ambient group used by the sourced permutation model. -/
abbrev J2Carrier : Type := Carrier

/-- The automorphism extension is the full automorphism group of the sourced
carrier, rather than an assumed semidirect product. -/
abbrev AutJ2Carrier : Type := MulAut Carrier

instance autJ2CarrierFinite : Finite AutJ2Carrier := inferInstance

abbrev S3 : Type := Equiv.Perm (Fin 3)
abbrev S5 : Type := Equiv.Perm (Fin 5)

/-! ### Intrinsic core descriptions -/

/-- A subgroup is the quaternion--dihedral central product occurring in the
Hall--Janko local calculation.  The factors and their common central
involution are retained, rather than replacing the group by an isomorphic
order-32 type. -/
def IsQuaternionDihedralCore {Q : Type*} [Group Q]
    (K : Subgroup Q) : Prop :=
  ∃ (B C : Subgroup K),
    Nonempty (B ≃* QuaternionGroup 2) ∧
    Nonempty (C ≃* DihedralGroup 4) ∧
    Nat.card (B ⊓ C : Subgroup K) = 2 ∧
    (∀ b ∈ B, ∀ c ∈ C, b * c = c * b) ∧
    B ⊔ C = ⊤ ∧
    Nat.card K = 32

theorem IsQuaternionDihedralCore.card
    {Q : Type*} [Group Q] {K : Subgroup Q}
    (h : IsQuaternionDihedralCore K) : Nat.card K = 32 := by
  rcases h with ⟨B, C, hB, hC, hI, hcomm, hspan, hcard⟩
  exact hcard

/-! ### The marked parabolic contracts -/

section Marked

/-- Common fields for a marked rank-two local model. -/
structure MarkedParabolics (G : Type*) [Group G] where
  l₁ : Subgroup G
  l₂ : Subgroup G
  s : Subgroup G
  b : Subgroup G
  p₁ : Subgroup G
  p₂ : Subgroup G
  s_le_b : s ≤ b
  s_le_l₁ : s ≤ l₁
  s_le_l₂ : s ≤ l₂
  b_le_p₁ : b ≤ p₁
  b_le_p₂ : b ≤ p₂
  p₁_eq_l₁b : p₁ = Subgroup.closure ((l₁ : Set G) ∪ (b : Set G))
  p₂_eq_l₂b : p₂ = Subgroup.closure ((l₂ : Set G) ∪ (b : Set G))
  overlap : p₁ ⊓ p₂ = b
  generated : Subgroup.closure ((p₁ : Set G) ∪ (p₂ : Set G)) = ⊤

namespace MarkedParabolics

variable {G : Type*} [Group G] (m : MarkedParabolics G)

/-- The subgroup amalgam is formed using the whole marked overlap `B`. -/
def amalgam : RankTwoAmalgam m.p₁ m.b m.p₂ :=
  RankTwoAmalgam.ofSubgroups _ _ _ m.b_le_p₁ m.b_le_p₂

theorem overlap_eq : m.p₁ ⊓ m.p₂ = m.b := m.overlap

theorem generated_eq :
    Subgroup.closure ((m.p₁ : Set G) ∪ (m.p₂ : Set G)) = ⊤ := m.generated

theorem left_injective : Function.Injective m.amalgam.left :=
  RankTwoAmalgam.ofSubgroups_left_injective _ _ _ m.b_le_p₁ m.b_le_p₂

theorem right_injective : Function.Injective m.amalgam.right :=
  RankTwoAmalgam.ofSubgroups_right_injective _ _ _ m.b_le_p₁ m.b_le_p₂

end MarkedParabolics

/-- The J₂ local calculation.  Quotient fields use the intrinsic core of the
numerator group.  The two-core of `L₂` has its cardinality recorded separately
because it is not determined by its quotient type alone. -/
structure J2LocalModel (G : Type*) [Group G] extends MarkedParabolics G where
  l₁_core : IsQuaternionDihedralCore (pCore 2 toMarkedParabolics.l₁)
  L₁_quotient : ClassicalGroup.IsPSL
    (toMarkedParabolics.l₁ ⧸ pCore 2 toMarkedParabolics.l₁) 2 4
  l₂_quotient : ClassicalGroup.IsPSL
    (toMarkedParabolics.l₂ ⧸ pCore 2 toMarkedParabolics.l₂) 2 2
  l₂_core_card : Nat.card (pCore 2 toMarkedParabolics.l₂) = 64

/-- The `Aut(J₂)` local calculation.  The first quotient is the quotient of
`L₁S`, as in the source, while the intrinsic core description remains that of
`L₁`. -/
structure AutJ2LocalModel (G : Type*) [Group G] extends MarkedParabolics G where
  l₁s : Subgroup G
  l₁s_eq : l₁s = toMarkedParabolics.l₁ ⊔ toMarkedParabolics.s
  l₁s_quotient : Nonempty
    ((l₁s ⧸ pCore 2 l₁s) ≃* S5)
  l₁_core : IsQuaternionDihedralCore (pCore 2 toMarkedParabolics.l₁)
  l₂_quotient : Nonempty
    ((toMarkedParabolics.l₂ ⧸ pCore 2 toMarkedParabolics.l₂) ≃* S3)
  l₂_core_card : Nat.card (pCore 2 toMarkedParabolics.l₂) = 64

end Marked

/-! ### Concrete model-indexed recognition predicates -/

section Predicates

variable {L B R : Type*} [Group L] [Group B] [Group R]

/-- Legacy local-shape predicate without an ambient-carrier identification.
It is not the source Hall--Janko alternative. -/
def IsJ2ParabolicModel
    (α : RankTwoAmalgam L B R) : Prop :=
  ∃ (G : Type) (_ : Group G) (m : J2LocalModel G),
    Nonempty (RankTwoAmalgam.ParabolicEquiv α m.toMarkedParabolics.amalgam)

/-- Legacy outer local-shape predicate; it does not identify `Aut(J₂)`. -/
def IsAutJ2ParabolicModel
    (α : RankTwoAmalgam L B R) : Prop :=
  ∃ (G : Type) (_ : Group G) (m : AutJ2LocalModel G),
    Nonempty (RankTwoAmalgam.ParabolicEquiv α m.toMarkedParabolics.amalgam)

end Predicates

end Sporadic.LeechRelated.J2
