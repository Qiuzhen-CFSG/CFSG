module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.Chapter12
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.GeometricComparisons

/-!
# The geometric U₅ profile at the original Chapter 12 consumer

The apartment quotient of the actual reduced amalgam supplies its own marking.
The mixed-factor profile constructs the U₅ comparison with the literal universal
quotient maps, and original-extension restoration returns the full original
amalgam comparison. Apartment geometry, root quotient data, splitting and the
earlier profile remain explicit source premises.
Source: DGS Theorem D and (15.2), pp.224–228; Aschbacher–Smith F.1.12 and 12.2.1.
-/

public noncomputable section
open Subgroup Subgroup.CosetGeometry Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.FongSeitzBinary.UnitaryPresentation
open ChapterF.Source.FongSeitzBinary.UnitarySource.Combined
open ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

universe u v w
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
  (hp : Group.IsPerfect R)
  (apartment : Set (SourceVertex (reducedAmalgam ![L,R] (Global.sourceS L H))))
  (length : ℕ)
  (hL : Function.Injective (reducedAmalgam ![L,R] (Global.sourceS L H)).left)
  (hR : Function.Injective (reducedAmalgam ![L,R] (Global.sourceS L H)).right)
  (hbase : ∀ i, base (Universal.cosetFamily
    (reducedAmalgam ![L,R] (Global.sourceS L H))) i ∈ apartment)
  (hdeg : TwoNeighborsIn
    (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))) apartment)
  (htrans : BasedPathTransitive
    (X := (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal)
    (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))) (length+1))
  (hline : NoBranchingIn
    (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))) apartment)
  (hunique : ApartmentsUnique
    (X := (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal)
    (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))) apartment (length+1))
  (hexchange : ChosenApartmentExchange
    (X := (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal)
    (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))) apartment length)
  (hlength : 1 < length)
  (hcore : ((Universal.left (reducedAmalgam ![L,R] (Global.sourceS L H))).range ⊓
    (Universal.right (reducedAmalgam ![L,R] (Global.sourceS L H))).range).normalCore = ⊥)
  (droot : RootQuotientData
    (quotientMap (reducedAmalgam ![L,R] (Global.sourceS L H)) apartment length))
  (hB : droot.B = originalMiddle (reducedAmalgam ![L,R] (Global.sourceS L H)))
  (hP : ∀ i, droot.endpoint i =
    Universal.cosetFamily (reducedAmalgam ![L,R] (Global.sourceS L H)) i)
  (hBN : droot.B.map
      (quotientMap (reducedAmalgam ![L,R] (Global.sourceS L H)) apartment length) ⊓
    droot.N.map
      (quotientMap (reducedAmalgam ![L,R] (Global.sourceS L H)) apartment length) =
    (droot.B ⊓ droot.N).map
      (quotientMap (reducedAmalgam ![L,R] (Global.sourceS L H)) apartment length))
  (split : SplitData (recognitionQuotient
    (reducedAmalgam ![L,R] (Global.sourceS L H)) apartment length
    hL hR hbase hdeg htrans hline hunique hexchange hlength hcore droot hB hP hBN).tits)
  (hrot : rotationOrder (recognitionQuotient
    (reducedAmalgam ![L,R] (Global.sourceS L H)) apartment length
    hL hR hbase hdeg htrans hline hunique hexchange hlength hcore droot hB hP hBN) = 4)

include D h hmany hn hpsl hH d hp hrot in
/-- The actual geometric quotient and its U₅ profile restore the whole
original Chapter 12 amalgam, without an additional marked-isomorphism premise. -/
theorem rankOne_comparison_of_geometric_unitary_five_profile
    (K : Type v) (E : Type w) [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2] (m : ℕ) (hm : 0 < m) (line : Bool)
    (p : FiveProfile ![L,R]
      (SuzukiContainment.reducedSylow ![L,R] (Global.sourceS L H))
      (recognitionQuotient (reducedAmalgam ![L,R] (Global.sourceS L H)) apartment length
        hL hR hbase hdeg htrans hline hunique hexchange hlength hcore droot hB hP hBN)
      split K E m (if line then 1 else 0) (if line then 0 else 1)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  let α := reducedAmalgam ![L,R] (Global.sourceS L H)
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hf := d.hypothesisF11 hi hH.1.1.2
  have hred := SuzukiContainment.reduced_hypothesis hf
  have hij : (if line then (1 : Fin 2) else 0) ≠ (if line then 0 else 1) := by
    cases line <;> decide
  obtain ⟨M, f, c, hBorel, hleft, hmiddle, hright⟩ :=
    geometric_unitaryFive_source_comparison_concrete α apartment length
      hL hR hbase hdeg htrans hline hunique hexchange hlength hcore droot hB hP hBN
      split ((intersectionToReduced hf).trans
        (geometricMarkedIso α apartment length hL hR hbase hdeg htrans hline hunique
          hexchange hlength hcore droot hB hP hBN))
      hred hrot m hm _ _ hij p
  have ci : Iso α (UnitaryFiveNative.amalgam M line) := by
    cases line <;> exact c
  exact d.concreteComparison_of_reduced_alternatives hi hH.1.1.2 hp
    (.unitaryFive (2^m)
      (Nat.prime_two.isPrimePow.pow (Nat.ne_of_gt hm))
      (even_two.pow_of_ne_zero (Nat.ne_of_gt hm)) M line ⟨ci⟩)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
