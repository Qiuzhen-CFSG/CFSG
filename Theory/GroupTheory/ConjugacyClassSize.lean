module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Conjugacy-class sizes under a surjective homomorphism

The size of the image class divides the size of the original class. This is
orbit–stabilizer and index divisibility: the centralizer of an element is
contained in the inverse image of the centralizer of its image. No finiteness
hypothesis is needed for the `Nat.card` formulation.

This elementary class-size formula supports inflation of central characters.
-/

namespace ConjClasses
variable {G K : Type*} [Group G] [Group K]

public theorem nat_card_carrier_eq_index_centralizer (g : G) :
    Nat.card (ConjClasses.mk g).carrier = (Subgroup.centralizer ({g} : Set G)).index := by
  calc
    _ = (MulAction.stabilizer (ConjAct G) g).index :=
      (congrArg (fun s : Set G => Nat.card s) (ConjAct.orbit_eq_carrier_conjClasses g)).symm.trans
        (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) g))
    _ = _ := (Subgroup.index_comap_of_surjective
      (MulAction.stabilizer (ConjAct G) g)
      (f := (ConjAct.toConjAct (G := G)).toMonoidHom)
      ConjAct.toConjAct.surjective).symm.trans
        (congrArg Subgroup.index (Subgroup.centralizer_eq_comap_stabilizer g).symm)

public theorem nat_card_carrier_map_dvd (f : G →* K) (hf : Function.Surjective f) (g : G) :
    Nat.card (ConjClasses.mk (f g)).carrier ∣ Nat.card (ConjClasses.mk g).carrier := by
  rw [nat_card_carrier_eq_index_centralizer, nat_card_carrier_eq_index_centralizer, ← Subgroup.index_comap_of_surjective _ hf]
  apply Subgroup.index_dvd_of_le
  intro x hx
  change f x ∈ Subgroup.centralizer ({f g} : Set K)
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  simpa only [map_mul] using congrArg f hx
end ConjClasses
