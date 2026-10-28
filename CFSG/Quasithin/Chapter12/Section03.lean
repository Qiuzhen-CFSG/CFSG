module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.Source
public import CFSG.Quasithin.Chapter12.Section03.WeightFour
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisFusion
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceOmega
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceSplitting
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceSubgroups
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceFive
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceConclusion
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceConclusion
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsQuotients
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsRemaining
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsBinaryLinear
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsSourceModels
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowNormalizer
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowOmegaSpan
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowOmegaAction
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentMaximal
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperRigidity
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperAction
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentResidualSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperNatural
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentAmbientUniqueness
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalModule
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsFirst
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Source

/-!
# Eliminating `A₇`: concrete module calculations

Aschbacher–Smith, *The Classification of Quasithin Groups*, §12.3,
printed pp. 807–812 (combined manuscript, 1 March 2004).

The local-analysis extension constructs the normalizer action and proves
fusion from full natural coordinates and structural 12.2.2, with the earlier
Sylow-normalizer bound now established in the natural A₇ branch.
Original 12.3.3 now supplies full natural coordinates, including the
four-dimensional exclusion, the cohomological lift and compatibility with
the original central quotient. The point-centralizer conclusion proves both
ambient weight-two and weight-six bounds and constructs LocalAnalysis from
the permitted earlier-source inputs and uniform natural coordinates.
The local-analysis source assembly discharges those uniform coordinates,
constructs LocalAnalysis for every original setup, and supplies the intersection
and weight-four escaping-point consumers without further local premises.
In the contrary Sylow-normalizer branch, the new quotient
extension proves the actual A₇ and A₆ two-core quotients. The component
extension constructs the C.2.3 setup in every fixed-coset centralizer and
excludes every actual C.2.7 star model, proving relative normality and
C-component membership throughout the coset. The source residual assembly
combines these results with A.3.18 to construct both literal ambient
residual identities, retaining the nonidentity restriction at fixed points.
The omega-span extension proves the actual bound |Ω₁Z(T)| ≤ 4|C_{Ω₁Z(T)}(L)|
under normalizer escape and supplies it to the marked-transport consumer.
The omega-action extension applies this transport to the A₅-in-A₆ obstruction,
discharging the Sylow-normalizer premise of ambient fusion. The residual
assembly supplies its ambient-residual input. The local-model extensions
identify the literal point quotients and prove the common two-core equality
through the original permutation action. The Sylow-normalizer assembly
therefore discharges all model, residual and omega-action inputs, leaving
only natural coordinates and the earlier structural theorem explicit.

The Thompson extension proves L=[L,J(T)], the full symmetric normalizer
action, and the full decomposition of the actual core omega center as
V ⊕ C_{Ω₁Z(T)}(L) from the weight-six centralizer input. The splitting uses
commutator generation, natural-module cohomology and the actual Sylow image,
retaining the central-cover kernel. The weight-two residual now has its literal
A₅ two-core quotient and the required disjoint factors. The conclusion
extension identifies the fixed space of its actual local two-core, proves
the point-residual Thompson equality by maximum-elementary Sylow transport,
and assembles both clauses of 12.3.7 under the weight-six input. The completed
point-centralizer argument discharges that input. In the weight-two branch,
the literal A₅ component on the omega span has an Irr⁺ moved module by the
full B.5 comparison. This identifies [U,K] with [V,K]; the natural commutant
and the original KTY cover then give the ambient bound in 12.3.8.

The terminal source extension constructs the escaping weight-four point,
its normal A₅ component, the central-cover reduction and the literal marked
S₅ × S₃ product. The B.5.6 decomposition then gives the weight-two centralizer
contradiction. The source assembly now constructs uniform local analysis and
the strict weak-closure bounds, leaving only structural 12.2.2, its seven module
alternatives and centralizer escape explicit. The Chapter13 adapter discharges
escape under Hypothesis 13.1.1 and the earlier Theorem 12.2.13.

The terminal maximal-component extension proves Thompson generation for the
actual residual and eliminates a doubled natural A₅ module by analyzing its
full linear normalizer. It supplies the maximal branch after the 12.2.7
residual quotient and one-or-two module alternatives have been constructed.

The weight-four subspace assertion used in the printed proof of Lemma 12.3.9
requires correction: the displayed plane extends to a binary simplex code.
The imported calculations establish this extension and the three possible
nonzero weights. The repaired argument proves the sufficient strict rank and
weak-closure bounds directly, including the simplex case; the assembly does
not assume the stronger rank-four bound of Lemma 12.3.9.
-/
