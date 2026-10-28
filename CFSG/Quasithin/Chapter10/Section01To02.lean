module

public import Theory.NumberTheory.BinaryMersenneDivisibility
public import Theory.GroupTheory.SubgroupPairCentralizers

/-!
# Chapter 10 preliminaries: arithmetic and centralizer bounds

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript, 1 March 2004, §§10.1–10.2, printed pp. 741–755.
The end of §10.2, including Corollary 10.2.13, is on printed p. 755.

The public imports provide the field-degree restriction used in Proposition
10.2.3 and the elementary centralizer, index, and conjugate-intersection
arguments in Proposition 10.2.9 and Lemma 10.2.10. The structural hypotheses
needed to apply them come from the chapter's nonnormal Fundamental Setup.

The section's final assembly is Corollary 10.2.13: combine the upper bound
`w(G,V) ≤ n(H) ≤ 2` from E.3.39 and 10.2.3 with the alternatives of 10.2.12.
The natural `L₂(4)` alternative is excluded by 10.2.3(4), leaving the natural
`L₃(2)` alternative with `w(G,V) = n(H) = 2`.
-/
