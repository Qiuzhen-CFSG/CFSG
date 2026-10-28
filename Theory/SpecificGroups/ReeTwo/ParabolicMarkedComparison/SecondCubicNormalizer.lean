module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicCentralizer
public import Theory.GroupTheory.OrderThreeNormalizer.Cardinality

/-!
# The native cubic normalizer

The genuine endpoint reflection inverts the native cubic. Its normalizer in
the second-core automorphism group therefore has order 96, twice the proved
centralizer order. Cubic Sylow conjugacy also makes the exact centralizer
order independent of the chosen element of order three.

Source: the binary Ree endpoint calculation for Aschbacher–Smith F.1.12/J.4.5.
-/

@[expose] public section
noncomputable section
namespace ReeTwo.SylowModel.CubicAction

open Subgroup
open Tits.AmalgamRigidity.FullRee.SecondExtension

theorem cubic_centralizer_card_of_order_three (γ:MulAut A) (hγ:orderOf γ=3) :
    Nat.card {α:MulAut A // Commute α γ}=48 := by
  obtain ⟨c,hc⟩:=firstParabolic_cubic_conjugacy γ cubic hγ cubic_order
  let ec:=MulAut.conj c
  let eqv : {α:MulAut A // Commute α γ}≃{α:MulAut A // Commute α (ec γ)} :=
    Equiv.subtypeEquiv ec.toEquiv (fun α=>(commute_map_iff ec.injective).symm)
  have he:=Nat.card_congr eqv
  change Nat.card {α:MulAut A // Commute α γ}=
    Nat.card {α:MulAut A // Commute α (c*γ*c⁻¹)} at he
  rcases hc with hc|hc
  · rw [hc] at he
    exact he.trans cubic_centralizer_card
  · rw [hc] at he
    simpa only [Commute.inv_right_iff] using he.trans (by
      simpa only [Commute.inv_right_iff] using cubic_centralizer_card)

def inverter : MulAut A := action reflection

attribute [local irreducible] action

theorem inverter_inverts : inverter*cubic*inverter⁻¹=cubic⁻¹ := by
  have hr:reflection⁻¹=reflection := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using weyl_relations.square)
  have hs:(inclusion (SylowModel.root 0))⁻¹=inclusion (SylowModel.root 0) := by
    rw [←map_inv]
    congr 1
  have he:reflection*element*reflection⁻¹=element⁻¹ := by
    simp only [element,mul_inv_rev]
    calc
      reflection*(inclusion (SylowModel.root 0)*reflection)*reflection⁻¹=
          reflection*inclusion (SylowModel.root 0) := by group
      _ = reflection⁻¹*(inclusion (SylowModel.root 0))⁻¹ := by rw [hr,hs]
  simpa only [map_mul,map_inv,inverter,cubic] using congrArg action he

theorem cubic_normalizer_card :
    Nat.card (normalizer (zpowers cubic:Set (MulAut A)))=96 := by
  rw [normalizer_card_of_order_three_inverter cubic inverter cubic_order inverter_inverts]
  have he : centralizer ({cubic}:Set (MulAut A))≃{α:MulAut A // Commute α cubic} :=
    Equiv.subtypeEquivRight (fun α=>mem_centralizer_singleton_iff)
  rw [Nat.card_congr he,cubic_centralizer_card]


end ReeTwo.SylowModel.CubicAction
