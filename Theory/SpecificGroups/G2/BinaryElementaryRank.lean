module

public import Theory.SpecificGroups.C4SquareSignSwapElementaryBound
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.FullSignSwap
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.ElementaryAbelian.Injective

/-!
# Elementary actors in the full binary G₂ group

Embed an elementary subgroup in a Sylow subgroup, transport it to the actual
common Sylow and then to its sign-and-swap coordinates. The elementary bound
in that model gives order at most eight and binary dimension at most three.
This concerns the full G₂(2) group, including its outer involutions.

Source: the rank calculation in Aschbacher--Smith 14.3.14, printed p.994.
The concrete Sylow equivalence is from the licensed ATLAS port; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public noncomputable section
namespace Atlas.G2
open Subgroup
open scoped IsMulCommutative

/-- An elementary two-subgroup of the full G₂(2) has at most eight elements. -/
theorem binary_elementary_card_le_eight (E : Subgroup (Model (ZMod 2)))
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 8 := by
  obtain ⟨P, hEP⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  let e := (P.equiv BinaryParabolicPair.commonSylow).trans
    BinaryParabolicPair.FullSignSwap.equiv
  let A := (E.subgroupOf P).map e.toMonoidHom
  let : IsElementaryAbelian 2 (E.subgroupOf P) :=
    IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hEP).toMonoidHom
      (subgroupOfEquivOfLe hEP).injective
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map e.toMonoidHom
  have hc := C4SquareSignSwap.elementary_card_le_eight A
  have he : Nat.card (E.subgroupOf P) = Nat.card A :=
    Nat.card_congr (e.subgroupMap (E.subgroupOf P)).toEquiv
  rwa [← he,
    Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv] at hc

/-- A literal elementary subgroup of any group isomorphic to full G₂(2)
has binary dimension at most three. -/
theorem binary_actor_finrank_le_three {D : Type*} [Group D] [Finite D]
    (e : D ≃* Model (ZMod 2)) (X : Subgroup D) [IsElementaryAbelian 2 X] :
    Module.finrank (ZMod 2) (Additive X) ≤ 3 := by
  let : IsElementaryAbelian 2 (X.map e.toMonoidHom) :=
    IsElementaryAbelian.map e.toMonoidHom
  have hc := binary_elementary_card_le_eight (X.map e.toMonoidHom)
  have he : Nat.card X = Nat.card (X.map e.toMonoidHom) :=
    Nat.card_congr (e.subgroupMap X).toEquiv
  rw [← he,
    Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

end Atlas.G2
