module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic

/-!
# Parabolic candidates attached to the fixed Ree unipotent pair

For either sign, take the intrinsic unipotent normalizer and adjoin the opposite
simple block. The simple block of the other sign lies in the intersection of
this subgroup with the other unipotent subgroup. Equality, maximality, and the
classification of normalizer overgroups require separate fixed-group geometry.

Pair preservation implies preservation of the two intrinsic normalizers by
functoriality of the normalizer. No identification with a torus or root Borel is
used. The exposed definitions let the later geometric proofs calculate these
particular subgroups directly, independently of final rigidity assembly.

Source: GLS3, §§2.3–2.5, especially 2.3.6–8 and 2.5.1.
-/

@[expose] public section
namespace ReeF4.LocalBlockInput.PairRigidity
open Subgroup LargeLocalSeeds
variable {m : ℕ}

/-- The specified member of the actual fixed unipotent pair; `true` is positive. -/
noncomputable def signedUnipotent (d : LocalBlockInput m) (positive : Bool) :
    Subgroup d.fixedGroup := if positive then standardUnipotent d else oppositeUnipotent d

/-- The intrinsic normalizer of a member of the unipotent pair.
Identifying it with a root-defined Borel is a separate geometric assertion. -/
noncomputable def signedBorelNormalizer (d : LocalBlockInput m) (positive : Bool) :
    Subgroup d.fixedGroup := normalizer (signedUnipotent d positive)

/-- Adjoin the opposite simple block to the unipotent normalizer.
Maximality and exhaustion of the overgroups of that normalizer are not assumed. -/
noncomputable def signedParabolic (d : LocalBlockInput m) (s : Side) (positive : Bool) :
    Subgroup d.fixedGroup := signedBorelNormalizer d positive ⊔ simpleBlock d s (!positive)

/-- Each block lies in its specified member of the unipotent pair. -/
theorem simpleBlock_le_signedUnipotent (d : LocalBlockInput m) (s : Side)
    (positive : Bool) : simpleBlock d s positive ≤ signedUnipotent d positive := by
  cases positive
  · exact simpleBlock_negative_le d s
  · exact simpleBlock_positive_le d s

/-- The easy containment in the opposite-parabolic intersection.
The reverse containment requires a genuine root-intersection calculation. -/
theorem simpleBlock_le_opposite_parabolic_inf (d : LocalBlockInput m) (s : Side)
    (positive : Bool) :
    simpleBlock d s positive ≤ signedUnipotent d positive ⊓ signedParabolic d s (!positive) := by
  refine le_inf (simpleBlock_le_signedUnipotent d s positive) ?_
  simpa only [signedParabolic, Bool.not_not] using
    (le_sup_right : simpleBlock d s positive ≤
      signedBorelNormalizer d (!positive) ⊔ simpleBlock d s positive)

/-- A pair-preserving automorphism preserves each signed unipotent subgroup. -/
theorem signedUnipotent_map (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (ha : d.PreservesUnipotentPair a) (positive : Bool) :
    (signedUnipotent d positive).map a.toMonoidHom = signedUnipotent d positive := by
  cases positive
  · exact ha.2
  · exact ha.1

/-- Preservation of a subgroup implies preservation of its intrinsic normalizer. -/
theorem signedBorelNormalizer_map (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (ha : d.PreservesUnipotentPair a) (positive : Bool) :
    (signedBorelNormalizer d positive).map a.toMonoidHom =
      signedBorelNormalizer d positive := by
  rw [signedBorelNormalizer, map_normalizer_eq_of_bijective _ a.bijective,
    signedUnipotent_map d a ha]

end ReeF4.LocalBlockInput.PairRigidity
end
