module

public import CFSG.Quasithin.ChapterE.Section05.Basic
public import CFSG.Quasithin.ChapterE.Section05.Containment
public import CFSG.Quasithin.ChapterE.Section05.RankBridge

/-!
# E.5: Weak closure and higher Thompson subgroups

This development proves Lemma E.5.5, including the quotient-action rank
bridge and its contrapositive used in 5.1.20. It also proves the normality
clause and initial containment steps of Proposition E.5.1, using the actual
rank-indexed Thompson groups from B.2.2.
The Frattini step of E.5.2 controls all its centralizers, and its E-generation
step reduces the conclusion to the explicit local two-residual bounds.
The local conjugate-centralizer cover and its rank estimate are proved;
E-member hypotheses supply the rank estimate on A∩O₂(K), so center containment
in Ω₁(Z(W)) now suffices for each local residual. The rank-degenerate
case of the generation assertion is also complete.

The omega-center containment in E.5.1, generation theorem E.5.2, solvable
corollary E.5.3, and no-FF-module alternative E.5.4 remain to be established.
The definitions exported here specify their subgroup constructions; they do
not assume those results.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, §E.5, printed pp.242–244.
-/
