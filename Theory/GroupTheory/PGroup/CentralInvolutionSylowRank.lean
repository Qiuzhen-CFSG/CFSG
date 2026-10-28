module

public import Theory.GroupTheory.PGroup.NormalEightCentralFour

/-!
# Elementary rank from central Sylow involutions

If every involution of a Sylow two-subgroup is central and its central first
omega subgroup has order four, every elementary binary subgroup of the ambient
group has order at most four. Embed an elementary subgroup in a Sylow subgroup,
transport it to the chosen Sylow subgroup, and contain its image in central
omega. This derives the rank bound instead of presupposing it.

This is a transfer of the intrinsic containment proved in
`NormalEightCentralFour`, used in the central-four specialization of
Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, p.386.
-/

open Subgroup

namespace Sylow

/-- Central Sylow involutions and central omega of order four bound all
ambient elementary binary subgroups by four. -/
public theorem elementary_card_le_four_of_central_involutions
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hc : ∀ x : S, orderOf x = 2 → x ∈ center S)
    (A : Subgroup G) [IsElementaryAbelian 2 A] : Nat.card A ≤ 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let E : Subgroup S := (A.subgroupOf T).map (T.equiv S).toMonoidHom
  let : IsElementaryAbelian 2 (A.subgroupOf T) := IsElementaryAbelian.subgroupOf hAT
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hle := card_le_of_le (elementary_le_omega_center_of_involutions_central E hc)
  have hcard : Nat.card E = Nat.card A := by
    rw [card_map_of_injective (T.equiv S).injective,
      Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv]
  rwa [card_map_of_injective (center S).subtype_injective, hZ, hcard] at hle

end Sylow
