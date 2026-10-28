module

public import Theory.Representation.BinaryNaturalDual.ModelOrbits
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.ModelOrbits.Source

/-!
# The actual model, invariant form and three vector orbits for H.9.1

This boundary exposes the constructed automorphism action, the actual layer
identification, and a comparison preserving both marked summands. From the
source group and natural-module hypotheses, `source_existsUnique_quadratic`
proves H.9.1(1), and `source_form_and_orbits` proves all of H.9.1(1–2).
The latter includes the three nonempty, disjoint orbits and the characterization
of singular diagonal vectors as nonzero vectors fixed by some Sylow subgroup.
It also retains transitivity by the actual layer on pairing-one vectors.

The reusable coordinate and transport APIs continue to take a specified
`BinaryNaturalDual.CoordinateAction`; the source theorem constructs that action
and discharges the comparison and standard Sylow fixed-line inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(1–2),
printed pp.389–390; see the H.9 source audit dated 6 October 2026.
-/
