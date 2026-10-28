module

public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Reduction

/-!
# Component enlargement and transfer: the group-theoretic reduction

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, 16.1.7–16.1.8, pp.1172–1173.

The actual enlargement is `ComponentTransfer.layerClosure (C_G(i)) L`.
The exports establish relative component restriction, the proper-overgroup
commutator identity, subnormality of a join of components, and the Sylow
restriction and centralizer-index comparison for this actual enlargement.
The geometric reduction is conditional on the stated ordinary specialization
of I.3.1–I.3.2; the chapter assembly must discharge that earlier premise.

This module does not yet assert 16.1.7 or `SmallCentralizerIndexTransfer`.
Completion requires the swapped-case family and solvable-residual calculation,
the nine intrinsic automorphism cases, and their strict Sylow-index bounds.
-/
