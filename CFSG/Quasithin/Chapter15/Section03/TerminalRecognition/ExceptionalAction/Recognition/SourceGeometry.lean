module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Reductions
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Theory.Representation.HexacodeAction

/-!
# The source definite plane inside the local quotient module

Restriction to `G₀` carries the actual plane supplied by the ambient natural
orthogonal action to a subgroup of `V ∩ G₀`. When `V ≤ G₀`, mapping it back
recovers exactly the original plane, and its order remains four. The same
restriction preserves the order sixteen of `V`.

The subgroup and its binary subspace in the normal-closure module have
identical underlying elements. Cardinality therefore gives binary dimensions
four and two for the vector group and its marked plane. A linear coordinate
change preserves the plane dimension. Finally, the quotient action is shown
to be the original ambient conjugation after both subgroup inclusions.
These facts keep the geometric marking intact; scalar stability and full
Hamming weight require the additional terminal recognition argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, the
plane decomposition on printed pp.1121–1122 and the final proof of 15.3.1
on printed p.1155 (PDF p.1172).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction

variable {G : Type*} [Group G] (G₀ M V : Subgroup G)

/-- The specific ambient definite plane, restricted to the actual local group. -/
noncomputable def localPlane (d : NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) : Subgroup G₀ := (d.plane i).subgroupOf G₀

/-- The restricted plane lies in the restricted vector group. -/
theorem localPlane_le (d : NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) : localPlane G₀ M V d i ≤ V.subgroupOf G₀ :=
  fun _ hx => d.plane_le i hx

/-- The subgroup inclusion recovers the original marked plane exactly. -/
theorem localPlane_map (d : NaturalOrthogonalAction M V)
    (hV : V ≤ G₀) (i : OrthogonalPlaneIndex) :
    (localPlane G₀ M V d i).map G₀.subtype = d.plane i :=
  map_subgroupOf_eq_of_le ((d.plane_le i).trans hV)

/-- Passage to the local group preserves the order of the marked plane. -/
theorem localPlane_card (d : NaturalOrthogonalAction M V)
    (hV : V ≤ G₀) (i : OrthogonalPlaneIndex) :
    Nat.card (localPlane G₀ M V d i) = 4 :=
  (Nat.card_congr (subgroupOfEquivOfLe ((d.plane_le i).trans hV)).toEquiv).trans
    (d.card_plane i)

/-- The natural vector group still has order sixteen inside the local group. -/
theorem localVector_card (d : NaturalOrthogonalAction M V) (hV : V ≤ G₀) :
    Nat.card (V.subgroupOf G₀) = 16 :=
  (Nat.card_congr (subgroupOfEquivOfLe hV).toEquiv).trans d.card_vector

variable {H : Type*} [Group H] (W : Subgroup H)
  [IsElementaryAbelian 2 (moduleClosure W)]

/-- The subgroup and its binary subspace have the same underlying elements. -/
noncomputable def planeSubspaceEquiv (P : Subgroup H) (hP : P ≤ moduleClosure W) :
    planeSubspace W P ≃ P where
  toFun v := ⟨v.val.toMul.val, v.property⟩
  invFun v := ⟨Additive.ofMul ⟨v, hP v.property⟩, v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Subgroup order determines the dimension of its actual binary subspace. -/
theorem planeSubspace_finrank_of_card [Finite H] (P : Subgroup H)
    (hP : P ≤ moduleClosure W) (n : ℕ) (hn : Nat.card P = 2 ^ n) :
    Module.finrank (ZMod 2) (planeSubspace W P) = n := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := planeSubspace W P)
  rw [Nat.card_congr (planeSubspaceEquiv W P hP), hn,
    Nat.card_eq_fintype_card, ZMod.card] at h
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) h).symm

variable [Finite G] [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]

/-- The source vector group is a four-dimensional subspace of its normal closure. -/
theorem localVectorSubspace_finrank (d : NaturalOrthogonalAction M V) (hV : V ≤ G₀) :
    Module.finrank (ZMod 2) (planeSubspace (V.subgroupOf G₀) (V.subgroupOf G₀)) = 4 :=
  planeSubspace_finrank_of_card _ _ le_normalClosure 4 (localVector_card G₀ M V d hV)

/-- The specified definite plane remains two dimensional in the normal closure. -/
theorem localPlaneSubspace_finrank (d : NaturalOrthogonalAction M V)
    (hV : V ≤ G₀) (i : OrthogonalPlaneIndex) :
    Module.finrank (ZMod 2) (planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)) = 2 :=
  planeSubspace_finrank_of_card _ _ ((localPlane_le G₀ M V d i).trans le_normalClosure)
    2 (localPlane_card G₀ M V d hV i)

/-- Every linear coordinate change preserves the dimension of this marked plane. -/
theorem localPlaneSubspace_map_finrank (d : NaturalOrthogonalAction M V)
    (hV : V ≤ G₀) (i : OrthogonalPlaneIndex)
    (e : Additive (moduleClosure (V.subgroupOf G₀)) ≃ₗ[ZMod 2] Atlas.Codes.hexacode) :
    Module.finrank (ZMod 2)
      ((planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map e.toLinearMap) = 2 := by
  rw [e.finrank_map_eq]
  exact localPlaneSubspace_finrank G₀ M V d hV i

omit [Finite G] in
/-- The local quotient action agrees with conjugation in the original ambient group. -/
theorem quotientAction_ambient_apply
    (hC : IsPGroup 2 (centralizer (V.subgroupOf G₀ : Set G₀)))
    (hcore : pCore 2 G₀ ≤ centralizer (V.subgroupOf G₀ : Set G₀))
    (g : G₀) (v : Additive (moduleClosure (V.subgroupOf G₀))) :
    (((quotientAction (V.subgroupOf G₀) hC hcore (coreProjection g) v).toMul : G₀) : G) =
      (g : G) * ((v.toMul : G₀) : G) * (g : G)⁻¹ :=
  congrArg G₀.subtype (quotientAction_apply (V.subgroupOf G₀) hC hcore g v)

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction
