module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Characteristic two of projective Borel preimages

The normalizer of any specified Sylow two-subgroup of PSL₃ over a finite
field of characteristic two has a self-centralizing two-core. Pulling back
along a surjection with two-group kernel preserves that property, hence
gives the genuine generalized-Fitting formulation of characteristic two.
This includes central two-covers without requiring a choice of lifts.

Source: the Borel calculation used in Aschbacher--Smith, 15.3.33(1) and
the proof of 15.3.38, printed pp.1134--1136. The matrix calculation is in
`BorelStructure`; the pullback argument is general finite-group theory.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.BorelStructure

variable (F : Type*) [Field F] [Finite F]
variable {J : Type*} [Group J] [Finite J]

/-- The full preimage of the specified projective Borel has characteristic two. -/
theorem sylowNormalizer_preimage_characteristicTwo {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (f : J →* PSL(3,F)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (P : Sylow 2 PSL(3,F)) :
    generalizedFitting ((normalizer (P : Set PSL(3,F))).comap f) =
      pCore 2 ((normalizer (P : Set PSL(3,F))).comap f) := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply f.centralizer_pCore_subgroup_of_image hk
  rw [map_comap_eq_self (by intro x _; exact hf x)]
  exact sylowNormalizer_core_selfCentralizing F hn hF P

/-- The same characteristic-two fact after an injective ambient embedding. -/
theorem sylowNormalizer_preimage_image_characteristicTwo
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (f : J →* PSL(3,F)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (P : Sylow 2 PSL(3,F))
    (i : J →* G) (hi : Function.Injective i) :
    generalizedFitting (((normalizer (P : Set PSL(3,F))).comap f).map i) =
      pCore 2 (((normalizer (P : Set PSL(3,F))).comap f).map i) := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply (Theory.Quasithin.centralizer_pCore_le_iff 2
    (((normalizer (P : Set PSL(3,F))).comap f).equivMapOfInjective i hi)).mp
  apply f.centralizer_pCore_subgroup_of_image hk
  rw [map_comap_eq_self (by intro x _; exact hf x)]
  exact sylowNormalizer_core_selfCentralizing F hn hF P

end Matrix.PSL3.LinearThree.BorelStructure
