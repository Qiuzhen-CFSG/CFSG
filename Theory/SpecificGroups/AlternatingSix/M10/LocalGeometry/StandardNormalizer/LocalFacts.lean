module
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.StandardNormalizer
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry

/-!
# Standard marked local facts with the normalizer premise discharged

Apply the full normalizer bound to the existing construction of the
semidihedral complement and its quaternion intersection. For an arbitrary
marking, the existing transport still requires simultaneous alignment and
normality of the specified extension; neither premise is asserted here.

Source: M. Aschbacher, A 2-local characterization of M12 (2003), beginning
of Lemma 4.9 and the choice of r in Lemma 4.10, pp.41–42.
-/

@[expose] public section
namespace AlternatingSix.M10.LocalGeometry

/-- All clauses of the standard marked geometry, with no additional premise. -/
noncomputable def standardLocalFactsProved : LocalFacts standardMarking :=
  standardLocalFacts standardNormalizer_upper

/-- Transport to an aligned source marking. The normalizer premise of the
original assembly is now discharged by the actual automorphism calculation. -/
theorem nonempty_localFacts_of_alignment (m : Marking)
    (hn : extension.Normal) (ha : Nonempty (PermutationAlignment m)) :
    Nonempty (LocalFacts m) := by
  obtain ⟨a⟩ := ha
  exact ⟨a.localFacts hn standardLocalFactsProved⟩

end AlternatingSix.M10.LocalGeometry
