module

public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.Transvections
public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.Seven
public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.PointOrbit
public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.PointStabilizers
public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.Orthogonal

/-!+# Transvections and small binary module recognition

B.4.10 and B.4.11 are proved with their actual source actions. Full root groups
induce GL on the orbit span, and the established A₇ spectrum gives dimension
four or six for every nontrivial irreducible binary module of degree at most
eight.

B.4.12(2)'s `FifteenPointStabilizerInput` is proved in `PointStabilizers`: the
literal subgroup actions in PSL₄(2) and A₇ transport to the original vector
orbit, giving two-transitivity and size fifteen. This discharges the action
premise of `lemma_B_4_12_two_of_stabilizers`.

B.4.13 still needs the local geometric embedding from `OrthogonalSeed`.
Its proved conditional assembly constructs a genuine equivariant linear
isomorphism of the original action with the marked orthogonal six-space;
it does not assert the remaining source theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.4.10–B.4.13, printed pp.96–98.
-/
