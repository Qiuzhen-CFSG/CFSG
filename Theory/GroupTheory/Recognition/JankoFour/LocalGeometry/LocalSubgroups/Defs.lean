module

public import Theory.GroupTheory.Recognition.JankoFour.LocalHypotheses
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.Intrinsic
public import Theory.Representation.MathieuCodeRestriction.Actions
public import Theory.Mathieu.M22.Properties.Automorphisms
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Marked algebraic subgroups for the type-J₄ geometry

These are output types for the local construction, not additional type-J₄
hypotheses. The point group is identified with the semidirect product for the
literal eleven-dimensional cocode action of the native M₂₄. The plane group is
the original involution centralizer. Its intersections with the point and line
groups are inverse images of actual hexad and pair stabilizers in Aut(M₂₂).
Thus the cubic kernel is retained in both intersections.

The line witness retains the special two-core and the actual L₃(2) and S₅
quotients. Subgroups of the line group, and normality in the point-line
intersection, are relative to those groups, not to the ambient group.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), §4; exposition,
*The study of J₄ via the theory of uniqueness systems*, (3.1), pp.16–17.
Existence of these output types remains a separate mathematical obligation.
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups

open Subgroup Sporadic.Mathieu
open scoped Pointwise

abbrev ToddVector := Multiplicative MathieuCode.Cocode

/-- The actual Todd action, including its native M₂₄ marking. -/
noncomputable def toddAction : M24 →* MulAut ToddVector where
  toFun g := (LinearMap.GeneralLinearGroup.toLinearEquiv
    (MathieuCode.cocodeRepresentation.asGroupHom g)).toAddEquiv.toMultiplicative
  map_one' := by
    ext v
    exact congrArg Multiplicative.ofAdd
      (LinearMap.congr_fun MathieuCode.cocodeRepresentation.map_one v.toAdd)
  map_mul' g h := by
    ext v
    exact congrArg Multiplicative.ofAdd
      (LinearMap.congr_fun (MathieuCode.cocodeRepresentation.map_mul g h) v.toAdd)

abbrev ToddGroup := ToddVector ⋊[toddAction] M24

/-- A stabilizer in the concrete design automorphism group, mapped into the
abstract automorphism group by its proved faithful conjugation action. -/
noncomputable def designStabilizer (B : Finset (Fin 22)) : Subgroup (MulAut M22) :=
  (MulAction.stabilizer m22DesignAut B).map m22DesignAutToAut

variable {G : Type*} [Group G] [Finite G] (z : G)

/-- Output of the point-subgroup construction, with its actual plane overlap.
No existence of this record is postulated. -/
structure PointData where
  cubic : CubicAutomorphismQuotient ((centralizer z) ⧸ core z)
  M : Subgroup G
  toddEquiv : ToddGroup ≃* M
  hexad : Finset (Fin 22)
  hexad_mem : hexad ∈ m22Blocks
  overlap : M.subgroupOf (centralizer z) =
    (designStabilizer hexad).comap (CubicLift.projection cubic)

namespace PointData

variable {z}

/-- The elementary normal subgroup embedded in the original ambient group. -/
noncomputable def vectorEmbedding (P : PointData z) : ToddVector →* G :=
  P.M.subtype.comp (P.toddEquiv.toMonoidHom.comp SemidirectProduct.inl)

noncomputable def E (P : PointData z) : Subgroup G := P.vectorEmbedding.range

theorem vectorEmbedding_injective (P : PointData z) :
    Function.Injective P.vectorEmbedding :=
  P.M.subtype_injective.comp (P.toddEquiv.injective.comp SemidirectProduct.inl_injective)

theorem E_le (P : PointData z) : P.E ≤ P.M := by
  rintro _ ⟨v, rfl⟩
  exact (P.toddEquiv (SemidirectProduct.inl v)).property

end PointData

/-- Output of the line-subgroup construction for the chosen marked point.
The compatibility equations are part of the output to be constructed. -/
structure LineData (P : PointData z) where
  G₂ : Subgroup G
  K : Subgroup G₂
  S : Subgroup G₂
  factorization : ∀ g : G₂, ∃ k : K, ∃ s : S, (k : G₂) * (s : G₂) = g
  intersection : K ⊓ S = pCore 2 G₂
  core_card : Nat.card (pCore 2 G₂) = 2 ^ 15
  core_commutator : commutator (pCore 2 G₂) = center (pCore 2 G₂)
  core_frattini : frattini (pCore 2 G₂) = center (pCore 2 G₂)
  center_elementary : IsElementaryAbelian 2 (center (pCore 2 G₂))
  center_card : Nat.card (center (pCore 2 G₂)) = 8
  linearQuotient : (K ⧸ (pCore 2 G₂).subgroupOf K) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)
  symmetricQuotient : (S ⧸ (pCore 2 G₂).subgroupOf S) ≃* Equiv.Perm (Fin 5)
  pair : Finset (Fin 22)
  pair_card : pair.card = 2
  pair_le_hexad : pair ⊆ P.hexad
  plane_overlap : G₂.subgroupOf (centralizer z) =
    (designStabilizer pair).comap (CubicLift.projection P.cubic)
  point_line_core : (pCore 2 (P.M ⊓ G₂ : Subgroup G)).map (P.M ⊓ G₂).subtype =
    P.E ⊔ (pCore 2 G₂).map G₂.subtype
  point_line_core_card : Nat.card (pCore 2 (P.M ⊓ G₂ : Subgroup G)) = 2 ^ 17
  linear_le_point_line : K.map G₂.subtype ≤ P.M ⊓ G₂
  linear_normal_point_line : ((K.map G₂.subtype).subgroupOf (P.M ⊓ G₂)).Normal
  pointLineQuotient :
    ((P.M ⊓ G₂ : Subgroup G) ⧸ pCore 2 (P.M ⊓ G₂ : Subgroup G)) ≃*
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3))

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
