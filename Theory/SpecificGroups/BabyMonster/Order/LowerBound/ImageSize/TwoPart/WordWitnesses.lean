module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.TwoPart.WordWitnesses.SectionWords

/-!
# Evaluation infrastructure for the Baby Monster two-part words

`WordWitnesses.Word.matrix_entry` certifies the packed entries of every word in
`standardImage`, using only the square/cube identities of the two fixed generators.
`WordWitnesses.max2Program` and `max4Program` reproduce the preserved ATLAS programs.

`WordWitnesses.sectionGenerator_entry` gives the exact entries of sixteen
explicit lifted section words. Their proposed role is recorded in
`WordWitnesses/source/README.md`.

A concrete family of 41 polycyclic generators and its collection/separation data
remain to be constructed. This module does not yet export that family or claim
that either candidate program generates a subgroup of the proposed order.
-/
