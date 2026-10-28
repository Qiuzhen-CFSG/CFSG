module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Source

/-!
# Local structure in the unique maximal two-local case

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 2.3.8(4–6), 2.3.9(1–6,8), and 2.3.10, printed pp.523–527.

Selection supplies precisely 2.3.8(1–3). This extension proves the
characteristic-normalizer containment, Thompson normalizer control, both
index-two β criteria, core-centralizer bounds, the literal hypotheses of
1.1.5, Sylow transport and central-Sylow geometry, characteristic two of
H ∩ M, and all of 2.3.10.

The block decomposition is constructed from the universal earlier Local
C(G,T) theorem C.1.29. The inversion and component embeddings use the
universal structural implications 1.1.5 and 1.2.4. The latter embedding
first gives a C-component and then proves it quasisimple using the checked
A.3.3 commutator dichotomy and Fitting-centralizer criterion. These earlier
universal inputs remain explicit pending their existing source owners;
this module does not assert their unconditional completion.

`componentRefinement_localSetup_of_sources` constructs the actual common
input of the independent 2.3.9(7) owner, including its local block generation.
The source-numbered conditional names identify their remaining source inputs.
Parent modules and their public re-exports are left to their assembly owners.
-/
