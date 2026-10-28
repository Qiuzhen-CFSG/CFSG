module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TriangleGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceWeylParameter

/-!
# Triangle geometry of the literal source apartment quotient

Apply the proved source equality between the apartment parameter and the
marked Weyl rotation order. At n=3 the same finite quotient has diameter
three and unique shorter geodesics on its full marked parabolic cosets.
The source path, reflection and exchange premises remain with their
existing producers. No quotient of the user's ambient completion is
postulated: the carrier here is the original universal apartment quotient.

Source: DGS, Groups and Graphs, (3.6)--(3.7) and Theorem D, pp.77--80,224;
the centerfree branch of (10.5), p.156.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan.A2Source
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
variable (roots : Bool → LocalRootAction (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)))

variable (hnormalizes : ∀ i, (roots i).reflection ∈
  Subgroup.normalizer (cartan c : Set (reducedAmalgam L S).Universal))

variable (ha : ∀ i, (roots i).a = Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L S)) i)
variable (hb : ∀ i, (roots i).b = Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (hinv : ∀ i, (roots i).reflection * (roots i).reflection = 1)
variable (n : ℕ) (hn : 1 < n)
variable (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
  p.IsPath → p.length = n+1 →
    Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)))
variable (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (n+1))
variable (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S))
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n)
variable (hsign : ∀ i x, x ∈ apartmentGroup c roots →
  (∀ r ∈ (roots i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n (x⁻¹*r*x) ∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n)) ∨
  (∀ r ∈ (roots i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n
    (((roots i).reflection*x)⁻¹*r*((roots i).reflection*x)) ∈
      (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
        (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n)))

open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Subgroup.CosetGeometry.RankTwo

include ha hb in
/-- The m=3 geometry on the same universal source quotient, using its proved parameter. -/
theorem finiteQuotient_triangle (hn3 : n = 3) :
    let d := finiteQuotient h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign
    (graph (TriangleGeometry.family d)).UniqueGeodesicsBelow 3 ∧
      ∀ v w, (graph (TriangleGeometry.family d)).dist v w ≤ 3 := by
  let d := finiteQuotient h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign
  have hm : RootCoordinates.rotationOrder d = 3 :=
    (finiteQuotient_simple_product_order h c roots hnormalizes ha hb hinv n hn hodd
      htrans hexchange hsign).trans hn3
  exact ⟨TriangleGeometry.uniqueGeodesicsBelow d hm, TriangleGeometry.diameter_le_three d hm⟩

end ReducedCartan.A2Source
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
