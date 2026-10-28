module

public import Theory.LinearAlgebra.QuadraticForm.SixTernaryCoordinates
public import CFSG.Quasithin.ChapterF.Section05.Source
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
public import CFSG.Quasithin.ChapterF.Section05.GraphRecognition
public import CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
public import CFSG.Quasithin.ChapterF.Section05.CompletionModel
public import CFSG.Quasithin.ChapterF.Section05.TriangleOrbit
public import CFSG.Quasithin.ChapterF.Section05.ModelSystem
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.Generation
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionClasses
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionFacts
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.SourceExceptional
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerCore
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerPlane
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerPointAction
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerFacts
public import CFSG.Quasithin.ChapterF.Section05.SourceSystem
public import CFSG.Quasithin.ChapterF.Section05.SourceSystemLocalMaps
public import CFSG.Quasithin.ChapterF.Section05.SourceSystemLocalOrbit
public import CFSG.Quasithin.ChapterF.Section05.SourceAmalgamRecognition
public import CFSG.Quasithin.ChapterF.Section05.SourceRecognition
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.ModelVertexProperness
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.SourceSmallRecognitionComplete

/-!
# The `U₄(2)` amalgam in `L₄(3)`: original source recognition

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §F.5, printed pp. 299–304.

The re-exported coordinate lemmas establish the eigenspace calculation for
Lemma F.5.1(3) and the sign-change centralizer and commutator calculations for
Lemma F.5.3(2),(6). The actual projective orthogonality graph is now proved
simply connected, as in F.5.8(2), and this supplies the geometric premise of
the terminal uniqueness-system recognition. The original marked source
hypotheses retain both normalizer equalities and the ambient two-residual.

The actual diagonal commutator model is now identified with PSL₄(3) and proved
simple, discharging both premises of the geometric completion consumer.
The concrete uniqueness system uses the standard triple stabilizer as its local
group. Its local triangle and transitive triangle action discharge all remaining
model-geometric premises.
The original hypotheses imply exceptionality by transfer. Controlled local
fusion and the graph-centralizer join supply a shorter global generation
argument. For the simple-group consumer, the source coset construction also
supplies faithfulness directly; its local maximality and marking inputs remain
with the local-group analysis.
The compatible-map construction now transports both local generation identities
from the concrete model, avoiding separate maximality inputs. Its ambient
recognition consumer retains the marked maps and their edge-conjugation identity.
Choosing the edge element through the local map also transports the local coset
action and discharges local edge-stabilizer preservation. All original F.5.4
normalizer facts are now proved from the source hypotheses.
The direct model-amalgam endpoint further removes construction of the source
coset system: two agreeing local maps and the marked reversal-conjugation
identity extend to the ambient group. Model simplicity and source generation
give the isomorphism, without source edge-intersection or maximality proofs.
The original local normalizer is now proved to be S₄ × S₄ with its actual
two-core. A graph-marked vertex comparison gives its properness by the
order-1440 model centralizer bound, and hence an oriented local comparison.
A plane-only inner adjustment of the source vertex comparison preserves the
literal graph, core and complementary S₄. The source cyclic root then corrects
the local comparison and gives pointwise agreement. Its image of the specified
model reversal is the root or its inverse. The actual D≃S₆ comparison now
supplies the fixed-endpoint involutions. Every element of R₀ centralizes the
corrected complement, and its cyclic generator supplies the graph square.
The model residual centralization and odd-index supplement discharge the
full edge-conjugation identity. The actual elementary-sixteen pair and its
order-nine normalizer actions exclude elementary R₀, yielding the cyclic-four
root. `source_ambient_equiv` therefore identifies the original ambient group
with PSL₄(3) from `Source.Hypotheses` alone. No local-recognition, compatible-map,
generation or geometric premise remains in that theorem.
-/
