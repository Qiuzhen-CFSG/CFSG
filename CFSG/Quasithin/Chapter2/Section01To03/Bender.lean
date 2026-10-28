module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.FamilyToLocal
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentActor
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ProjectedComponent
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.AlternatingInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.OddCharacteristicInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.EvenCharacteristicInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.InnerAction
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.OmegaNormalizer
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.G2Inspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.G2SimpleInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.G2BinaryInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.TrialityInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.TitsInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.ReeInspection.UnipotentCenter
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.BinaryLinearInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.SymplecticInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MathieuInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MathieuTwelveInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MathieuRemainingInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.JankoTwoInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.JankoFourInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.HigmanSimsInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.HeldInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.RudvalisInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.InnerAlternatingInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.BadCentralizers
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.OrdinaryBalance
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.GoodCentralizers
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.GoodCentralizers.ZD

/-!
# The Bender reduction: proved local control and conditional component geometry

The literal Alperin–Goldschmidt family gives Proposition 2.2.2(1), and the
source He comparison gives Lemma 2.2.3 and local control from empty δ.
The component modules prove the intersection argument and its actual GO
application. The projected-component module constructs the internal-product
split from actual inner-action witnesses and transports the full normalizer
action image, with the earlier component and model facts explicit.
After the genuine odd-core elimination, abelian strong closure now forces
U to normalize every component of the actual involution centralizer. The
proof retains central products and uses Burnside transfer on the central
quotient; it requires no component classification.
The marked alternating and triple-cover rows are excluded. The inner
odd-characteristic row reduces to PSL₂(5), using actual involution fusion
and Sylow presentations while preserving the original distinguished z.
The even-field PSL₃ family is excluded as well, including the central-two
PSL₃(4) covers. The actual quotient kernel is derived from the odd-core
hypothesis, and returning quotient conjugates lift inside the original
component Sylow; no involutory implementer lift is assumed.
The central-two G₂(4) covers are also excluded using only the marked
two-central root class and two noncommuting returning conjugates. No
kernel-order, global fusion or block-generation premise is required.
The same uniform root argument excludes ordinary G₂(2ᶠ) for f≥2 with the
source simplicity hypothesis. Binary PSL₄(2) and PSL₅(2) are excluded using
the original Sylow-central transvection class and a noncommuting pair in a
nested-radical two-subgroup. The derived G₂(2)′ case is excluded using
conjugators inside the actual commutator subgroup; field transport preserves
every field-order-two source model. Binary triality is excluded uniformly,
including q=2, by its Sylow-center coordinates and internal Weyl conjugations.
The Tits derived group is excluded by an internal Parrott conjugator and
a single-point permutation certificate for the noncommuting marked pair.
The large Ree groups are excluded by internal Weyl conjugations and positive
root commutators. The proved standard unipotent-center identification supplies
the original marker, with no additional center or involution-class premise.
The even Sp₄ family is excluded by a two-step returning-product argument.
Ratios of returning marked conjugates cancel their common centralizing factor
and put a second marker in U; its noncommuting returning pair contradicts
abelianness. Only the original central marker uses the Sylow-center coordinates.
The M₁₁ quotient in the marked sporadic row is excluded through the same
returning-conjugate argument, using its proved semidihedral Sylow and
involution fusion. The original bad-centralizer application retains the
full central two-kernel.
The M₁₂ quotient is excluded by embedding a marked M₁₁ pair and using the
proved fusion of involution squares. The actual Sylow-central marker has
that class; no assertion that all M₁₂ involutions are conjugate is used.
The remaining M₂₂, M₂₃ and M₂₄ quotients are excluded through genuine
PSL₃(4) and point-stabilizer embeddings. In M₂₄ the embedded pair and the
original two-central marker are proved to belong to class 2A. Thus all
Mathieu cases in the marked sporadic row now have source consumers.
The J₂ and HS quotients are excluded by two explicit conjugates in each
actual Sylow. Existing intrinsic marker results identify their classes;
small checked permutation identities supply the noncommuting pairs.
The J₄ pair uses two small kernel-coordinate calculations and the known center
of an actual Sylow. Held uses its internal fusion words and one permutation
point. Rudvalis uses an actual Tits pair: fixed points identify its involution
class, and the marked Sylow center identifies the original source marker.
These source consumers retain every allowed central two-kernel and the literal
centralizer and component inclusions.
The inner A₆ occurrence is excluded using its dihedral Sylow and involution
fusion, including the literal PSp₄(2)′ and PSL₂(9) source equivalences. The
original marker and bad-centralizer Sylow embeddings are retained.
For a selected Bender model, the whole-U action now has actual implementers
in the first omega of the component Sylow. Returning marked conjugates give
omega containment in U, and strong closure supplies the square-one
displacements used to exclude outer unitary actions. Both implementer
directions are supplied to the existing component contradiction.
The selected model also supplies centerlessness, omega size, transitivity,
and the cyclic odd full normalizer action image. Rank-one Sylow geometry
identifies the omega normalizer with the Sylow normalizer, retaining the
unitary norm-one kernel. The resulting source consumer requires no additional
intrinsic model-geometry premise.

BadCentralizers now constructs the actual bad-centralizer setup, eliminates
the odd core, aligns the Sylow and selects a maximal component. Uniform
U-normalization supplies the ordinary balance application, and the full
six-case sieve applies the completed model inspections. Its empty-delta
consumer proves all required centralizer containments from the genuine
universal 1.1.5(3) and ordinary I.3.1(1),(2) implications. Those two earlier
source theorems remain to be supplied. GoodCentralizers constructs literal
product disconnection and applies simple Corollary ZD to the original G and M.
Its marked empty-delta application identifies M as the Sylow normalizer and
a Borel subgroup, retains the actual Bender model and field exponent, and
proves U is the first omega and embedded center of the original Sylow.
The full ZD conclusion now supplies the exact simple corollary through the
original closure and quotient maps. Final assembly must still supply the two
earlier component implications and Theorem ZD. The general Shult covering alternatives are unnecessary
for this simple ambient-group application.
-/
