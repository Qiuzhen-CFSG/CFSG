module
public import Theory.SpecificGroups.AlternatingSix.M10.Contracts
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.Canonical
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.Transport
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.StandardNormalizer
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.MarkingConjugacy

/-!
# Assembly of the marked M₁₀ local geometry

The concrete holomorph embedding constructs the semidihedral complement,
its center and quaternion intersection, and the involution needed in 4.10.
The full standard-normalizer calculation and simultaneous conjugacy of the
source marking discharge the two geometric premises of the construction.

The resulting `nonempty_localFacts` supplies the exact `LocalFacts` consumed
by `SymmetricNormalizerData.m10GeometryOfModelFacts`. Its only premise beyond
the source marking is normality of the fixed extension, supplied by that
consumer's independently constructed `ActionFacts.normal`.

Source: M. Aschbacher, A 2-local characterization of M12, Illinois J. Math.
47 (2003), beginning of 4.9 and choice of r in 4.10, pp.41–42.
-/

@[expose] public section
namespace AlternatingSix.M10.LocalGeometry
open Subgroup ShadowLocal

/-- All standard local clauses, conditional only on the full-normalizer
upper bound. The complement and quaternion isomorphism are constructed. -/
noncomputable def standardLocalFacts
    (hN : normalizer (nine standardNine : Set AutA6) ≤
      nine standardNine ⊔ standardComplement) : LocalFacts standardMarking where
  P := standardComplement
  card_P := card_standardComplement
  semidihedral := standardComplement_semidihedral
  normalizer_eq := le_antisymm hN standardNormalizer_lower
  disjoint := standardComplement_disjoint
  z_mem := standardZ_mem_complement
  center_P := center_standardComplement
  quaternion := ⟨standardQuaternionEquiv⟩
  b_mem := marked_b_mem standardMarking
  r := Identification.reflection
  r_mem := reflection_mem_extension
  r_sq := by simpa only [pow_two] using Identification.reflection_sq
  r_not_mem_P := reflection_not_complement
  r_not_mem_stabilizer := reflection_not_stabilizer
  r_normalizes_P := reflection_normalizes_complement

/-- Exact assembly for an arbitrary source marking, retaining the two
geometric inputs as an interface for the separate calculations. -/
theorem nonempty_localFacts_of_normalizer_and_alignment (m : Marking)
    (hn : extension.Normal)
    (hN : normalizer (nine standardNine : Set AutA6) ≤
      nine standardNine ⊔ standardComplement)
    (ha : Nonempty (PermutationAlignment m)) : Nonempty (LocalFacts m) := by
  obtain ⟨a⟩ := ha
  exact ⟨a.localFacts hn (standardLocalFacts hN)⟩

/-- Every source marking has the complete concrete local geometry, assuming
only normality of the specified extension. The standard normalizer and the
simultaneous marking alignment are both constructed. -/
theorem nonempty_localFacts (m : Marking) (hn : extension.Normal) :
    Nonempty (LocalFacts m) :=
  nonempty_localFacts_of_normalizer_and_alignment m hn standardNormalizer_upper
    (nonempty_permutationAlignment m)

end AlternatingSix.M10.LocalGeometry
