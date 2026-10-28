module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.Statement
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Assembly
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SymmetricFiveAssembly

/-!
# Applying the orbit theorems to the literal classification rows

The natural A₅-cover and deleted S₅ outputs of 13.1.10 retain the action
markings used by the completed orbit calculations. These applications
discharge the corresponding centralizer-analysis premises on the original
U and XiP quotients. The natural-cover row also supplies the source
quaternion sieve and its irreducible-component exclusion.

The remaining L₃(2) classification-to-action transports and the deleted-S₅
Sylow-action clause stay with qt-d-1317-module-orbits. The earlier Control
premise and the final 13.1.7 assembly stay with qt-d-1317-source.

Source: Aschbacher--Smith 13.1.10 and 13.1.12, printed pp.871--874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The first classification row supplies the two exact sieve interfaces. -/
theorem PSLTwoFourMarking.centralizer_inputs
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (d : PSLTwoFourMarking T L W) (h : Context T L p) :
    OrbitFacts T L p ∧ SieveActions h :=
  ⟨d.natural.orbitFacts h,d.natural.sieveActions h⟩

/-- The natural-cover classification row eliminates the original
irreducible escaping component, retaining only earlier source control. -/
theorem PSLTwoFourMarking.not_escape_of_irreducible
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (d : PSLTwoFourMarking T L W) (h : Context T L p) (c : Control T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) : False :=
  d.natural.not_escape_of_irreducible h c s hnt e hi

/-- The second classification row supplies radical irreducibility, the
selected index bound and the original fixed-core identity. -/
theorem SymmetricFiveRow.orbitFacts (d : SymmetricFiveRow T L)
    (h : Context T L p) : OrbitFacts T L p :=
  d.marking.orbitFacts h

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
