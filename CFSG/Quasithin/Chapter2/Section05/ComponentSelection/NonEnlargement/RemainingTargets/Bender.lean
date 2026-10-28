module
public import Theory.GroupTheory.SylowIntersectionSections
public import Theory.SpecificGroups.Classical.BinarySymmetricFour
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.BenderSylow
public import CFSG.Quasithin.ClassicalModels
/-!
# The complete Bender target exclusion for binary rank-two covers

Every actual Bender model, including binary PSU₃, has trivial intersections
of distinct Sylow two-subgroups. A subgroup and then its central two-quotient
inherit this property. Both prescribed binary rank-two quotients contain
an actual S₄, which contradicts that Sylow intersection property.
The original injection and center are retained; no multiplier, splitting,
subgroup classification or Sylow-normalization hypothesis is added.

Source: Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
variable {K C : Type*} [Group K] [Finite K] [Group C] [Finite C]
omit [Finite K] in
/-- No central two-cover of either specified binary rank-two quotient embeds
in any of the three literal Bender families. -/
theorem not_injective_bender (hZ : IsPGroup 2 (center K)) {n : ℕ}
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n) ∨
      ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n))
    (ht : ClassificationModels.IsBenderModel C) (f : K →* C) :
    ¬Function.Injective f := by
  intro hf
  have hK := SylowIntersection.of_injective f hf
    (bender_sylow_eq_of_inf_ne_bot ht)
  have hk : IsPGroup 2 (QuotientGroup.mk' (center K)).ker :=
    (QuotientGroup.ker_mk' (center K)).symm ▸ hZ
  have hQ := SylowIntersection.of_surjective (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective (center K)) hk hK
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact SylowIntersection.not_of_symmetric_four_embedding
      (Theory.SpecificGroups.Classical.BinarySymmetricFour.linear F)
      (Theory.SpecificGroups.Classical.BinarySymmetricFour.linear_injective F)
      (SylowIntersection.of_injective e.symm.toMonoidHom e.symm.injective hQ)
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact SylowIntersection.not_of_symmetric_four_embedding
      (Theory.SpecificGroups.Classical.BinarySymmetricFour.symplectic F)
      (Theory.SpecificGroups.Classical.BinarySymmetricFour.symplectic_injective F)
      (SylowIntersection.of_injective e.symm.toMonoidHom e.symm.injective hQ)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
