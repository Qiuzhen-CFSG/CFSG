module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Constructions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Orbit

/-!
# The block census needed for the residual fusion argument

`BlockCensus` specifies the output of the local calculation on the actual
block `C_P(D)V`: an elementary group of order 64 and its four conjugation
orbits, of lengths 9, 6, 12 and 36. Both inside orbits generate `V`.
It is a contract for a still separate calculation, not a source hypothesis
or a proof of that calculation.

The proved implication below combines a census with a block normalizer
moving `V` and the earlier separation of `z` and `v`. The normalizer
construction is deliberately independent of the orbit calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1151.
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03.FusionCore
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
variable {G : Type*} [Group G]

/-- Precise output of the local block calculation, for the actual conjugation action. -/
structure BlockCensus (I P V D : Subgroup G) (z v : G) where
  model : fusionBlock P V D ≃* Multiplicative (Fin 6 → ZMod 2)
  normalizes_block : I ≤ normalizer (fusionBlock P V D : Set G)
  normalizes_V : I ≤ normalizer (V : Set G)
  z_mem : z ∈ V
  v_mem : v ∈ V
  outside₁ : G
  outside₂ : G
  outside₁_mem : outside₁ ∈ fusionBlock P V D
  outside₂_mem : outside₂ ∈ fusionBlock P V D
  outside₁_not_mem : outside₁ ∉ V
  outside₂_not_mem : outside₂ ∉ V
  z_card : Nat.card {x : G // ConjugateBy I z x} = 9
  v_card : Nat.card {x : G // ConjugateBy I v x} = 6
  outside₁_card : Nat.card {x : G // ConjugateBy I outside₁ x} = 12
  outside₂_card : Nat.card {x : G // ConjugateBy I outside₂ x} = 36
  z_span : closure {x | ConjugateBy I z x} = V
  v_span : closure {x | ConjugateBy I v x} = V
  cover : ∀ x ∈ fusionBlock P V D, x ≠ 1 →
    ConjugateBy I z x ∨ ConjugateBy I v x ∨
      ConjugateBy I outside₁ x ∨ ConjugateBy I outside₂ x

/-- The final four-orbit argument applies to a calculated block census. -/
theorem block_cover_of_census [Finite G] (I P V D : Subgroup G) (z v : G)
    (c : BlockCensus I P V D z v)
    (hmove : ∃ g ∈ normalizer (fusionBlock P V D : Set G),
      g ∉ normalizer (V : Set G))
    (hsep : ¬ IsConj z v) :
    ∀ x ∈ fusionBlock P V D, x ≠ 1 → IsConj x z ∨ IsConj x v :=
  two_class_cover_of_four_orbits I V (fusionBlock P V D) z v c.outside₁ c.outside₂
    c.normalizes_V le_sup_right c.z_mem c.v_mem c.z_span c.v_span c.cover hmove hsep

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
