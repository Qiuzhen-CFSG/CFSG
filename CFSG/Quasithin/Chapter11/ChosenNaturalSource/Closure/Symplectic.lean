module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Algebra
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Core
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.BlockClosure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CoreAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.OddIndex
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.MSPair
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.RootOrbit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.RootClosure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.DistanceClosure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.OriginalDistance

/-!
# The symplectic closure argument from preceding source geometry

The original marked flag, core transfer from KY, opposite-pair core algebra,
and the corrected identification O₂(L)=V are available here. The latter uses
short-group irreducibility and the genuine core-commutator identity, avoiding
the false printed H¹ vanishing step. The W=U branch has trivial Frattini
subgroup; the source's subsequent argument only needs containment in V₁.

The full-cover radical action proves U abelian and supplies the literal
root action for the opposite-pair construction. Their combined application
places O₂(L) inside O₂(G₁), with the preceding Cartan, flag and 11.5.6 inputs
explicit. The characteristic reduction proves the two possible Q₁ action
images, the full-image intersection R₁ ∩ LQ₁ = Q₁, and MS3 inside the
literal LQ₁. In the full-image case, (L₁T) ∩ LQ₁ is the proper odd-index
subgroup with two-core Q₁ required by MS2(a). Its marked opposite pair
generates LT with L₁T and admits no
nontrivial characteristic subgroup of Q₁ normalized by that pair.
All MS-pair hypotheses now hold for the original LQ₁ in the full-image
case. In the root-image case, Q₁ is Sylow in IQ₁, which is SQTK of
characteristic two. The actual C.1.29 ordered block product and C.1.27
residual orbit are available for this same marked opposite pair. Its
residual is a single short block, and its original-core commutator bound
propagates through the simple symplectic quotient to give O₂(L)=V.

The terminal geometry now retains C_V(L). Displacement modulo V₁ suffices
for the literal intersection-plane and reverse-transporter arguments.
The noncommuting branch is excluded without a block premise, and the
commuting branch gives abelianness from the original core equality. This
closes the root-image branch. In the full-image branch, nonabelianness of the
original closure forces critical distance two for a minimum characteristic
replacement. Indeed V lies in its central-omega orbit, whereas at larger
distance an abelian characteristic edge layer contains every G₁-conjugate
of V. The distance-two whole-core theorem then supplies shortness at the
original field degree, which suffices for O₂(L)=V.

`abelian_of_preceding` proves the symplectic branch of 11.5.7 with only the
explicit preceding source geometry and conclusions through 11.5.6. The
original block-classification and conditional distance interfaces remain
available; the general MS classification and its field-four restriction are
not needed for this source-specific closure argument. The parent closure
owner retains discharge of the earlier source hypotheses.
Source: Aschbacher--Smith 11.5.7, printed pp.782--784.
-/
