module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.RestrictionBounds

/-!
# Two additional endpoint automorphisms sufficient for Tits rigidity

The proposed generator-image pairs are (69,1024) for the first endpoint and
(76,1168) for the second, in the existing normal-form coordinates for s3,s8.
The contracts below require actual Sylow automorphisms extending across the
literal endpoint inclusions. They do not assert that these witnesses exist.

The two pairs occupy indices 1024 and 1161 in the certified candidate table.
Both fail its compatibility mask. The fusion theorem therefore proves that
an extension at the stated endpoint cannot extend at the opposite endpoint.
Together with the common restriction subgroup of order 2048, such a witness
would give at least 4096 restrictions at its endpoint.

Source context: Parrott (1972), §5, p.683; Aschbacher--Smith F.1.11--12,
printed pp.262--263. The pairs were discovered by the reproducible GAP script
in ../source/explore_restrictions.py; the mask checks here are kernel proofs.
-/

@[expose] public section
noncomputable section
namespace Tits.AmalgamRigidity
open ExceptionalParabolics SharpOuterBound SharpOuterBound.LocalImageBound

private theorem pair_excludes_intersection (i : Fin 8192)
    (hi : allowedIndex i = false) (f : MulAut S)
    (hf : generatorPair f = candidatePair i) :
    f ∉ firstRestrictions ⊓ secondRestrictions := by
  intro hm
  have hc : HasCompatibleParabolicExtensions f :=
    (restrictionIntersectionEquiv ⟨f, hm⟩).property
  obtain ⟨hfirst, hsecond⟩ := compatible_fusionConditions f hc
  rw [hf] at hfirst hsecond
  exact Bool.false_ne_true (hi.symm.trans (candidatePair_allowed_of_fusion i hfirst hsecond))

/-- Missing first endpoint witness: an actual extension with the specified images. -/
def FirstExtraExtension : Prop :=
  ∃ f : MulAut S, f ∈ firstRestrictions ∧ generatorPair f = (69, 1024)
/-- Missing second endpoint witness: an actual extension with the specified images. -/
def SecondExtraExtension : Prop :=
  ∃ f : MulAut S, f ∈ secondRestrictions ∧ generatorPair f = (76, 1168)

/-- The first proposed extension cannot extend across the second inclusion. -/
theorem first_pair_not_second (f : MulAut S) (hf : f ∈ firstRestrictions)
    (hpair : generatorPair f = (69, 1024)) : f ∉ secondRestrictions := by
  have hi : allowedIndex 1024 = false := by decide +kernel
  have hp : candidatePair 1024 = (69, 1024) := by decide +kernel
  exact fun hs => pair_excludes_intersection 1024 hi f (hpair.trans hp.symm) ⟨hf, hs⟩

/-- The second proposed extension cannot extend across the first inclusion. -/
theorem second_pair_not_first (f : MulAut S) (hf : f ∈ secondRestrictions)
    (hpair : generatorPair f = (76, 1168)) : f ∉ firstRestrictions := by
  have hi : allowedIndex 1161 = false := by decide +kernel
  have hp : candidatePair 1161 = (76, 1168) := by decide +kernel
  exact fun hs => pair_excludes_intersection 1161 hi f (hpair.trans hp.symm) ⟨hs, hf⟩

end Tits.AmalgamRigidity
