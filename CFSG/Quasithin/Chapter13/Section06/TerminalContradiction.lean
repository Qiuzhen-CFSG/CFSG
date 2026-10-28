module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Parameters
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceKernel
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ContextComplete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ContextKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ParametersKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ComponentAssembly
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ResidualSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523Complete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.J2Complete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.J2LocalKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ExceptionalKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalCatalogue
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalEscape
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ClassificationComplete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourcePairOriginal
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelQuotientAction
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelSourceSemisimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelSourceConstituents
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.OriginalSource523
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourceSylow
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ActorNoSource523
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523Application
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523CartanEscape

/-!
# The A₅ terminal argument

The singular-intersection and commuting-conjugate conclusions of 13.6.24
are proved from their precise earlier inputs in `WeakClosure`, including
the concrete binary quadratic form and its singular-point calculation.
`Coordinates` transports the proved model orbits through actual conjugation,
identifies the actor kernel, and establishes F.9.8(g)(i) from 13.2.3(2).

The legacy `Parameters` interfaces remain reexported, but their additional
normalizer, fixed-space and residual assumptions do not establish the source
implications 13.6.25--26. Those source proofs remain with their assembly owner;
the precise discrepancies are recorded in `docs/quasithin-proof-basis.md`.

`Ratio.SourceKernel` proves the terminal module-ratio contradiction from
the actual earlier local, component and classification inputs. It discharges
F.9.2(3) using the proved kernel theorem on the literal F.9.1 setup.
The marked source application below supplies 13.5.7 and F.9.16(3).
Its native PSL₃(4), M₂₃ and J₂ bounds also discharge the strict module-ratio
input. The earlier 13.6.27 component conclusion remains explicit.

`SourceParameters.OriginalTerminal` applies the proved source orbit and
generation results to the literal component and Suzuki-join consumers. Its
terminal application uses the original marked A₅ setup and discharges B.4.2
from the complete known-simple classification. The native source application
below additionally supplies its B.4.5 bound.

`SourceRecognition.ContextComplete` constructs the coordinates and full
fusion control, then supplies the abelian closure and original 13.5.7 family.
Only the earlier A.3.12 input, nonsingular centralizer bound, singular
centralizer escape, counterexample and component conclusion remain.
`ContextKnownSimple` removes A.3.12 from this action argument, and
`ParametersKnownSimple` removes it from the original parameter setup:
both use the proved common-normal theorem in the earlier A₅ recognition.
`JankoFourKnownSimple` excludes the final actual normal J₄ component using
its faithful source action and concrete quadratic-ratio bound, removing the
full A.3.12 premise from the terminal catalogue conclusion. The J₂
branch in `J2LocalKnownSimple` starts from the original local component and
requires neither A.3.12 nor a 5.2.3 classifier; its uniqueness argument uses
the odd-rank isolation in `J2Complete`.
`SourceRecognition.ParameterSetup` also constructs the full earlier-source
parameter record from that same context. It supplies 13.6.25, the initial
residual in the original line centralizer and the large-prime core exclusion.
`ResidualSource` proves both 13.6.26 clauses on the original context and feeds
the remaining exceptional candidate and uniqueness to the 13.6.27 extension.
The large-prime residual has a three-free two-perfect image in S₅ normalized
by the actual A₅ Sylow four-group. Its triviality gives the original residual
normality and vanishing, removing the universal 13.3.8 input from this step.
`Source523Complete` also constructs component uniqueness by applying the
genuine earlier 5.2.3 classification and excluding its global alternatives
with the original ambient hypotheses. Its terminal theorem retains the
actual exceptional candidate and earlier centralizer/classification inputs.
The component-isolation source constructs the genuine mixed A₅–Suzuki
F.1.1 pair. Its Suzuki-side Sylow factorization now proves the Borel
normality required by F.1.12; exclusion of that pair remains an earlier
classification input.
Its original 5.2.3 application now constructs the full setup and all
ancillary source inputs, retaining the genuine classifier and its global
alternatives.

`SuzukiIsolation.BorelSourceSemisimple` proves semisimplicity of the actual
scalar extension of U_H/V₁ under a normal extra Suzuki component. The full
Borel fixes every original seed, and the normal-component span fills the
section. `BorelSourceConstituents` identifies all its simple constituents as
trivial or full Steinberg, retaining one compatible original quotient marking.
The original kernel identity, containment in H and solvable-overgroup conclusion
remain the precise source inputs. Constructing the subsequent isotypic action
and terminal contradiction remains separate.

`SourceRecognition.ActorNoSource523` supplies the extra-Suzuki-component
contradiction using the bounded original actor and the literal Suzuki
centralizer. This removes the second component-uniqueness use of the earlier
5.2.3 classifier; its candidate-selection use remains explicit.

`SourceRecognition.Source523Application` excludes the PSL₃(4) residual
directly in the original singular centralizer. Its conditional catalogue
application retains only the two non-linear source branches, split by
normalization of the residual by the image of N_L(T∩L). Both branches remain
earlier classification obligations; no universal A.3.12 input is needed.

`SourceRecognition.Source523CartanEscape` supplies the nonnormalization
callback from the shared generic Cartan source arguments. It derives the
multiple-overgroup guard from the actual HStar member and transports the
full relative component and quotient models to the chosen A₅ module.
The local and local-to-global Cartan arguments and the separate normalized
global branch remain explicit source obligations.

`SourceRecognition.ClassificationComplete` constructs the exceptional
candidate itself. The selected nonsolvable residual normalizes its unique
containing component; the A₇ generation bound excludes that quotient, and
E.2.2 supplies the actual linear diagram action. The full A.3.12 embedding
sieve lifts the candidate to a normal quasisimple component of the original
line centralizer, accepting a containing M₂₃ component directly. The terminal
ratio argument then excludes the whole local alternative. The remaining
full 5.2.3 global alternatives give an actual Main Theorem model and guarded
known-simple membership. Thus no component candidate or structural instance
remains an input. The genuine A.3.12 and 5.2.3 inputs and the two centralizer
conditions are still required. This catalogue endpoint retains field-two
rank-two models, rather than asserting the strict field bound of Theorem D.

`OriginalCatalogue.source_qtkeModel_of_A5_context` consumes the completed
J₄ exclusion and retains the two non-counterexample models directly in the
full catalogue. The A₅ context therefore needs neither model exclusions nor
an embedding callback. The original nonsingular centralizer bound, singular
escape and genuine 5.2.3 theorem remain the source inputs for final assembly.

`SourceRecognition.OriginalEscape` transports the genuine 12.2.13 escaping
vector through the two nonzero A₅ orbits and derives the singular centralizer
escape required by the catalogue. It retains 12.2.13 and 5.2.3 as explicit
source inputs.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §13.6, printed pp.933–935.
-/
