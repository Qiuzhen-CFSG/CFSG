module

public import Theory.GroupTheory.PRadicalParabolicReduction

/-!
# Borel--Tits and p-radical normalizers

This module currently exports the finite p-radical reduction: once a parabolic
contains the normalizer of a p-radical subgroup and its unipotent radical
contains that subgroup, the two radicals coincide and the parabolic equals
the normalizer. An ambient Sylow subgroup in the parabolic also gives the
chosen Sylow containment for an extremal p-radical subgroup.

The algebraic Borel--Tits existence theorem and its Steinberg-invariant form
remain prerequisites; this module does not assert them from the finite
reduction alone.

Source: GLS, *The Classification of the Finite Simple Groups*, volume 3,
Section 3.1, especially Theorems 3.1.1 and 3.1.3 and Corollary 3.1.5.
-/
