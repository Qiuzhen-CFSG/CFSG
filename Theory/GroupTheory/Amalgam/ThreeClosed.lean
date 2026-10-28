module

public import Theory.GroupTheory.SylowThreeCubic
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A small overlap from two normal cubic subgroups

Conjugation embeds the overlap of two finite groups into the product of
the automorphism groups of their normal order-three subgroups, provided
their common centralizing kernel is trivial. Each cyclic cubic group has
two automorphisms, so the overlap has order at most four.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.16)(b),
printed p.386. The kernel-vanishing premise is supplied either by an
intrinsically faithful amalgam or by a faithful connected graph action.
-/

public section
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G]

/-- The common normalizer-kernel criterion bounds the overlap of local groups
with normal cubic subgroups, without requiring a chosen ambient completion. -/
theorem overlap_card_le_four_of_normal_three
    (L R : Subgroup G) [Finite L] [Finite R]
    (X : Subgroup L) (Y : Subgroup R) [X.Normal] [Y.Normal]
    (hX : Nat.card X = 3) (hY : Nat.card Y = 3)
    (hkernel : ∀ K : Subgroup G, K ≤ L ⊓ R →
      X.map L.subtype ≤ normalizer (K : Set G) →
      Y.map R.subtype ≤ normalizer (K : Set G) → K = ⊥) :
    Nat.card (L ⊓ R : Subgroup G) ≤ 4 := by
  let : IsCyclic X := isCyclic_of_prime_card hX
  let : IsCyclic Y := isCyclic_of_prime_card hY
  let E := L ⊓ R
  let l : E →* L := Subgroup.inclusion inf_le_left
  let r : E →* R := Subgroup.inclusion inf_le_right
  let a : E →* MulAut X := (MulAut.conjNormal : L →* MulAut X).comp l
  let b : E →* MulAut Y := (MulAut.conjNormal : R →* MulAut Y).comp r
  let ρ := a.prod b
  let K := ρ.ker.map E.subtype
  have hK : K = ⊥ := by
    apply hkernel K (map_subtype_le _)
    · apply le_centralizer_iff.mp ?_ |>.trans (centralizer_le_normalizer _)
      rintro k ⟨k, hk, rfl⟩ x ⟨x, hx, rfl⟩
      have hka : a k = 1 := congrArg Prod.fst hk
      have hmem : l k ∈ centralizer (X : Set L) := by
        rw [← MulAut.conjNormal_ker_eq_centralizer]
        exact hka
      exact congrArg (fun z : L => (z : G)) (hmem x hx)
    · apply le_centralizer_iff.mp ?_ |>.trans (centralizer_le_normalizer _)
      rintro k ⟨k, hk, rfl⟩ y ⟨y, hy, rfl⟩
      have hkb : b k = 1 := congrArg Prod.snd hk
      have hmem : r k ∈ centralizer (Y : Set R) := by
        rw [← MulAut.conjNormal_ker_eq_centralizer]
        exact hkb
      exact congrArg (fun z : R => (z : G)) (hmem y hy)
  have hker : ρ.ker = ⊥ := (map_eq_bot_iff_of_injective _ E.subtype_injective).mp hK
  have hi : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hker
  have hcard := Nat.card_le_card_of_injective ρ hi
  simpa only [Nat.card_prod, IsCyclic.card_mulAut, hX, hY,
    Nat.totient_prime (by decide : Nat.Prime 3)] using hcard

end Subgroup
