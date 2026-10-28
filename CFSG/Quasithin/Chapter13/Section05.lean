module

public import CFSG.Quasithin.Chapter13.Section05.SourceAssembly.Prepared
public import CFSG.Quasithin.Chapter13.Section05.SourceAssembly.A5Abelian
public import CFSG.Quasithin.Chapter13.Section05.SourceDefs
public import CFSG.Quasithin.Chapter13.Section05.LocalSteps
public import CFSG.Quasithin.Chapter13.Section05.Endgame
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPairCompletion
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointCentralizer
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBNPair
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrdinaryEndpoints
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrdinaryRecognition
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledAmalgam
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalRecognition
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalKnownSimple
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefSieveComplete
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SourceRecognition
public import CFSG.Quasithin.Chapter13.Section05.A5Source.PointRecognition
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.SourceElimination

/-!
# The A₅ and A₆ branches with nonabelian V₃-closure

The target is Theorem 13.5.12: under Hypothesis 13.3.1, with
L/C_L(V) ≅ A_n for n = 5 or 6, excluding Sp₆(2), a nonabelian
⟨V₃^{G₁}⟩ gives U₄(2) or L₄(3) for n = 5 and U₄(3) for n = 6.
`ModelConclusion` uses actual projective matrix group isomorphisms.

This module currently exports the strict-span deduction of 13.5.9,
the F.9 application in 13.5.10, the conditional normalizer deductions of
13.5.18–19 and component selection after 13.5.20, and the final subgroup obstructions in
13.5.23 and 13.5.25. Their stated earlier hypotheses remain explicit.
It also constructs the original normal A₅ quaternion pair and embeds the
actual starred group into Ω₄⁺(2), with its order dividing 36. The pair
quotient is S₃ and its literal Sylow intersection is self-normalizing,
supplying the rank-one and Borel clauses used in 13.5.17.
The pair is normal in H and gives H=L₁IT. Its residual centralizes C_T(L₁),
which eliminates C_T(L) and proves O₂(LT)=O₂(N_G(L))=V, together with
N_G(V)=N_G(L)=LT and C_G(V)=V.
The normal A₅ source also proves O₂(H)=U_H, H=C_G(V₁), and
H_z={C_G(V₁)}, supplying the literal involution-centralizer and
module-normalizer premises used in 13.5.17.
The same chosen pair now satisfies genuine F.1.1, with common Borel L₁T
and parabolics H and LT. Their intersection is L₁T, and the literal
inclusion amalgam is faithful. Both ordinary parabolics now have literal
unitary model equivalences preserving V₁, V and their overlap subgroup.
Their restrictions are compatible on the common overlap, and the faithful
completion identifies the ambient group with the actual U₄(2) model in the
ordinary branch, giving `ModelConclusion G 5`. The doubled branch now also
has the exact compatible extended amalgam and the genuine F.5 completion
hypotheses, with the original endpoint ranges and root images. The proved
F.5 recognition identifies the doubled ambient group with PSL₄(3), completing
the original normal-L₁ theorem 13.5.17. It supplies every normal-recognition
call in the nonnormal component selection and chief sieve. The same selected
normal branch is exported by `A5Source.source13_5_17_knownSimple` with the
earlier A.3.12 input discharged by proved seed control over the complete
known-simple catalogue. Its `source13_5_18_knownSimple` excludes relative
normality in the degree-five counterexample branch. The same selected
star component is simple; it contains L₁ and is normal in H.
Its natural central quotient has the S₆, A₈ or G₂(2)′ action. The source
chief count, original core orders and order-four cubic fixed point exclude
those three rows. The known-simple seed-normalizer theorem removes the
earlier A.3.12 input. Nonabelianness supplies point-family membership, giving
`A5Source.source_point_modelConclusion_knownSimple` on the original point normalizer.
The new SourceAssembly exports also recognize the original A₅ point
closure without either escape or A.3.12 as a premise. They prove the
Section 13.6 abelian closures and two-core containment under the actual
model exclusions. The ordinary natural-six branch now gives positive
U₄(3) recognition, retaining only its prepared data, actual ordinary
quotient and earlier local maximality. Full source preparation and the
triple-cover A₆ branch remain necessary for Theorem 13.5.12.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
§13.5, printed pp.915–925 (PDF pp.932–942).
-/
