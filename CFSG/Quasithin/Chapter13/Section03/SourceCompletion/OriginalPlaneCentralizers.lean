module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.FinalAssembly
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.LinearThree.CubicLength
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.LinearThree.DoubledNatural
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.ResidualAssembly

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Assembly
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.Sylow
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.Fitting
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.Components
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.CubicResidual

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.ExtractedAssembly
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Normality
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Alternating
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Lie
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Actions

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.FieldParity
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.HigherRankOne

/-!
# Original nondegenerate-plane centralizers and source consumers

Exports the original-module applicability, compatible plane charts, literal
perpendicular four-space and complete rank-one endpoint for 13.3.12(2).
The actual plane centralizer has characteristic two, and its intersection
with M has faithful module-action quotient of order dividing six.
The original Q is radical in the plane centralizer and Sylow in its normal
closure in C_M(A), giving the actual C.2.3 setup. The fixed-vector bound
proves J(S)=J(Q) and constructs a Sylow subgroup of C_G(A) inside M.
Hyperplane centralizer control proves s(G,V)>1; solvable E-generation
then puts the actual plane-centralizer Fitting preimage inside M.
A.4.4 and the cubic action now extract an escaping quasisimple relative
C-component. The normalized branch supplies LocalData; the moved branch
retains its full Sylow intersection. An actual second cubic in N_G(A) outside
C_G(A) and the nonnormal-component residual theorem reduce the moved branch
to a three-free two-core quotient. The full-Sylow C.1.29 argument excludes
that branch, completing `Context.localExtraction`. The actual C.2.7 star
catalogue also proves that every LocalData component is normal in N_G(A).
The actual quotient of N_G(A) by the embedded component two-core then
excludes the A₆, A₇, A₈ and triple-six star rows, retaining the possible
central three-covers throughout the comparison. The resulting star catalogue
is specialized to the same plane, component and original Q. The actual central
covers and cubic residuals also exclude the large symplectic and G₂ families,
G₂(2)′ and SL₅(2). Applying these exclusions to the full moved-section action
leaves the natural linear-two and linear-three rows, doubled linear-three,
and symmetric-five. The linear-two row supplies Q Sylow in JQ and the
marked Borel, together with the original L₂-even/A₅ block alternative.
The full B.5 source conclusion is retained for the field reductions.
The actual module centralizer has order prime to three. Its plane-action
quotient then bounds the three-part of the star intersection, excluding
even-degree linear-three fields. The selected full Sylow excludes the
A₅ block and reduces the A₅ star alias to an actual L₂(4) block.
Rank intersection places the specified order-three cubic in both J and L;
the original perpendicular four-space now excludes that L₂(4) block.
The cubic normalizes the original radical Q, so the remaining natural
rank-one field degrees are even and at least four. The actual Borel residual then excludes
every higher-field rank-one block: it fixes V but has no noncentral fixed
vector in the natural block containing the marked perpendicular sixteen-group.
Only the two odd-degree linear-three moved sections remain, with their
full B.5 source data and original component markings.
The original component is now identified with the prime-to-three residual,
its quotient is SL₃(2), and all binary MS hypotheses hold on the literal JQ.
The marked perpendicular E16 forces the doubled-natural whole commutator
core, elementary of order 64, using the checked original-plane specialization.
This step retains the chosen relative Sylow and common quotient marking;
no universal binary MS classification premise remains. The exact cubic
lengths on Q, V and Q/V are three, two and one. The nontrivial cubic action
on the literal Q/V survives its Frattini quotient and descends through
L/O₂(L) to G₂(2)′. Its fixed codimension is at most two, contradicting the
unitary chief-factor bound. This completes the plane-centralizer conclusion
and discharges its premise in both original strict-rank and unitary-exclusion
consumers. The independent earlier Structural1222/catalogue and final
odd-normalizer inputs remain with their source assembly owners.
The original conditional public interfaces are preserved.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890.
-/
