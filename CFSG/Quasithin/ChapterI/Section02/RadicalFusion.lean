module

public import Theory.GroupTheory.PRadicalSubgroupFusion
public import Theory.GroupTheory.WeakClosureSylowTransport

/-!
# Structural fusion bridge for Aschbacher--Smith I.2.5

The imported subgroup-fusion theorem reduces the Lie-type conjugation-family
claim to identifying nontrivial p-radical subgroups with parabolic radicals.
The Sylow transport theorem shows that a radical's membership in one such
family suffices for every unipotent overgroup. It also forces every Sylow
subgroup containing the radical into its normalizer, supplying the membership
step for the families over arbitrary containing Sylow subgroups.

The finite Lie-type realization, Borel--Tits identification and reversal of
normalizer inclusions are still separate structural prerequisites. This module
does not assert I.2.5 without them. The Frattini transfer theorem records the
additional condition needed when applying the result in automorphism extensions.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma
I.2.5, printed p. 414/PDF p. 425; applications in Chapters 10, 12 and 14.
-/
