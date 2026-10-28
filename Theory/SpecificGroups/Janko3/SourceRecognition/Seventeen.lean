module

public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Completion
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.MarkedAction
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.PairEmbedding
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.ComplementConjugacy
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Alignment
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Recognition

/-!
# Baumeister's seventeen-point amalgam: source data and graph arguments

This boundary exports Lemma 2.7 and Corollary 2.8 from the literal source
hypotheses. The actual H₃ subgroup supplies a triangle in the connected
valency-sixteen coset graph. The graph is complete and its action faithful
and triply transitive of degree seventeen, with the two source stabilizers
marked and ambient order 8160. Every faithful completion has the universal
mapping property. Lemma 2.9 is proved by simultaneous point/overlap conjugacy and rigidity
of the pair subgroup. The same permutation in Sym(17) conjugates both
subgroup images. The resulting completion isomorphism can preserve a
specified overlap involution. The actual fourth-power-Frobenius PSL₂(16):2
model now supplies every source marking. Corollary 2.10 identifies every
faithful completion with this model while preserving the point and pair
groups and a prescribed overlap involution.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), pp.497–498.
-/
