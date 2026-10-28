module
public import Theory.Representation.BinaryPermutation.FiveInvariantHyperplane
public import Theory.ElementaryAbelian.Basic

/-!
# Displacement by an even involution on the binary five-point core

A nonidentity even involution has displacement image of order four. A
bounded check of the five-point permutations and sixteen vectors proves
this once; an injective equivariant embedding transfers the order bound
to the actual group commutator.

Application: the intersection of the two original natural modules in
Aschbacher--Smith 13.2.8(1), printed p.880.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace BinaryPermutation.FiveEvenDisplacement
abbrev U := Multiplicative (core (Fin 5))
def displacement (g : Equiv.Perm (Fin 5)) : U →* U where
  toFun v := Multiplicative.ofAdd (coreRepresentation (Fin 5) g v.toAdd - v.toAdd)
  map_one' := by simp
  map_mul' v w := by
    change Multiplicative.ofAdd (coreRepresentation (Fin 5) g (v.toAdd+w.toAdd) - (v.toAdd+w.toAdd)) = _
    simp only [map_add]
    change _ = Multiplicative.ofAdd ((coreRepresentation (Fin 5) g v.toAdd - v.toAdd) +
      (coreRepresentation (Fin 5) g w.toAdd - w.toAdd))
    congr 1
    abel
local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype U := inferInstanceAs (Fintype (core (Fin 5)))
private theorem computation : ∀ g : Equiv.Perm (Fin 5),
    g ≠ 1 → g^2 = 1 → g.sign = 1 →
    (Finset.univ.image (displacement g)).card = 4 := by decide +kernel

theorem card_range (g : Equiv.Perm (Fin 5)) (hne : g ≠ 1)
    (hp : g^2 = 1) (he : g ∈ alternatingGroup (Fin 5)) :
    Nat.card (displacement g).range = 4 := by
  have hs : (Set.range (displacement g)) =
      (Finset.univ.image (displacement g) : Set U) := by simp
  change Nat.card (Set.range (displacement g)) = 4
  rw [Nat.card_congr (Equiv.setCongr hs),Nat.card_coe_set_eq,Set.ncard_coe_finset]
  exact computation g hne hp (Equiv.Perm.mem_alternatingGroup.mp he)

theorem four_le_card_commutator {D : Type*} [Group D] [Finite D]
    (i : U →* D) (hi : Function.Injective i) (x : D)
    (g : Equiv.Perm (Fin 5)) (hne : g ≠ 1) (hp : g^2=1)
    (heven : g ∈ alternatingGroup (Fin 5))
    (he : ∀ v : U, i (Multiplicative.ofAdd (coreRepresentation (Fin 5) g v.toAdd)) =
      x * i v * x⁻¹) : 4 ≤ Nat.card (⁅zpowers x,i.range⁆ : Subgroup D) := by
  have hle : ((displacement g).range).map i ≤ ⁅zpowers x,i.range⁆ := by
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    have h : i (displacement g v) = ⁅x,i v⁆ := by
      change i (Multiplicative.ofAdd (coreRepresentation (Fin 5) g v.toAdd) / v) = _
      rw [map_div,he]
      simp only [div_eq_mul_inv,commutatorElement_def]
    rw [h]
    exact commutator_mem_commutator (mem_zpowers x) ⟨v,rfl⟩
  have hc := card_le_of_le hle
  rwa [card_map_of_injective hi,card_range g hne hp heven] at hc
end BinaryPermutation.FiveEvenDisplacement
