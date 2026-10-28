module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.Application
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.GeometricQuotient

/-!
# Triality recognition for the literal apartment-exchange quotient

The geometric quotient marking is composed with the proved root-presentation
comparison, using its actual universal-completion quotient. Both endpoint
orientations give the genuine triality catalogue row. All three maps are
restrictions of the same quotient equivalence: their generic representative
formulas and whole-overlap squares are those of `RootData.comparison`, and
the original universal inclusions are retained by `geometricMarkedIso`.

The carrier-general boundary is explicit before specializing to the geometric
marking, avoiding repeated elaboration through the universal pushout. The
source field equations, split data and root placements remain explicit inputs.
Source: DGS Theorem D, printed p.224, and its apartment-exchange construction.
-/

@[expose] public noncomputable section
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Subgroup.CosetGeometry RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation.Geometric
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
universe u
variable {A C E : Type u} [Group A] [Group C] [Group E] [Finite A] [Finite E]
  (α : RankTwoAmalgam A C E)
  (hL : Function.Injective α.left) (hR : Function.Injective α.right)
  (T : Set (SourceVertex α)) (n : ℕ)
  (hbase : ∀ i, base (Universal.cosetFamily α) i ∈ T)
  (hdeg : TwoNeighborsIn (sourceGraph α) T)
  (htrans : BasedPathTransitive (X := α.Universal) (sourceGraph α) (n+1))
  (hline : NoBranchingIn (sourceGraph α) T)
  (hunique : ApartmentsUnique (X := α.Universal) (sourceGraph α) T (n+1))
  (hexchange : ChosenApartmentExchange (X := α.Universal) (sourceGraph α) T n)
  (hn : 1 < n)
  (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
  (roots : RootQuotientData (quotientMap α T n))
  (hB : roots.B = originalMiddle α)
  (hP : ∀ i, roots.endpoint i = Universal.cosetFamily α i)
  (hBN : roots.B.map (quotientMap α T n) ⊓ roots.N.map (quotientMap α T n) =
    (roots.B ⊓ roots.N).map (quotientMap α T n))

local notation "geoQ" => recognitionQuotient α T n hL hR hbase hdeg htrans hline
  hunique hexchange hn hcore roots hB hP hBN
-- The concrete geometric marking is inserted only after the carrier-general comparison.

variable {F : Type*} [Field F] {σ : F ≃+* F} {m : ℕ} {hm : 0 < m}
  {armIndex : Fin 2}

/-- The literal geometric marking, without any descent to an unrelated ambient completion. -/
def comparison (e0 : RankTwoAmalgam.Iso α (geoQ).standardAmalgam)
    (split : SplitData (geoQ).tits) (d : RootData geoQ split m hm σ armIndex) :
    RankTwoAmalgam.Iso α (flagAmalgam m hm armIndex) :=
  RootData.comparison (X := α.Universal) (Psrc := recognitionEndpoints α)
    (Q := geoQ) (split := split) (F := F) (σ := σ) (α := α) d e0

/- The carrier-general comparison restricts one ambient equivalence to all three maps. -/
/-- Specialization to the literal apartment-exchange quotient and marking. -/
def geometricComparison (split : SplitData (geoQ).tits)
    (d : RootData geoQ split m hm σ armIndex) :=
  comparison α hL hR T n hbase hdeg htrans hline hunique hexchange hn hcore roots hB hP hBN
    (geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore roots hB hP hBN)
    split d

/-- Any original or geometric marking supplies the exact catalogue row. -/
theorem concreteComparison (e0 : RankTwoAmalgam.Iso α (geoQ).standardAmalgam)
    (split : SplitData (geoQ).tits)
    (d : RootData geoQ split m hm σ armIndex) : Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison α :=
  RootData.concreteComparison (X := α.Universal) (Psrc := recognitionEndpoints α)
    (Q := geoQ) (split := split) (F := F) (σ := σ) (α := α) d e0

/-- The apartment-exchange quotient supplies the triality catalogue row. -/
theorem geometricConcreteComparison (split : SplitData (geoQ).tits)
    (d : RootData geoQ split m hm σ armIndex) :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison α :=
  concreteComparison α hL hR T n hbase hdeg htrans hline hunique hexchange hn hcore roots hB hP hBN
    (geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore roots hB hP hBN)
    split d

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation.Geometric
