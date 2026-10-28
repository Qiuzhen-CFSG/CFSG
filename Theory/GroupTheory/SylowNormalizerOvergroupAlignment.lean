module

public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# Aligning ambient Sylow normalizers inside an overgroup

If a subgroup contains the ambient normalizer of one ambient Sylow subgroup,
then it contains the ambient normalizer of every ambient Sylow subgroup it
contains. Conjugate the two Sylow subgroups inside the overgroup and transport
their full normalizers. Consequently, coverage by a conjugate proper parabolic
also covers a prescribed Sylow normalizer whenever the standard Sylow
normalizer lies in that parabolic.

This module re-exports the common Sylow-normalizer lemmas. Keeping their
declarations in `SylowNormalizerOvergroup` lets the classical and exceptional
parabolic covers be imported together. In both lemmas the standard Sylow
subgroup precedes the prescribed Sylow subgroup.

This is the Sylow-conjugacy step in the defining-characteristic parabolic
argument of Aschbacher--Smith, 15.3.43(e), printed p.1140.
-/
