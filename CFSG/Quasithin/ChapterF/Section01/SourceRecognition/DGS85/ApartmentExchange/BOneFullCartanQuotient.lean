module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneFullCartanPaths

/-!
# The marked finite quotient for both natural source path lengths

The actual whole-Cartan reflections and the chosen source length r=3 or r=4
feed the existing geometric quotient construction. The paired Chapter 10
profiles supply the exact source parameters, next-path transitivity, odd
next-path fixers and thickness. Both oriented endpoint equations, the entire
original Borel and both inclusion squares are retained. Splitness includes
normality of the two-subgroup, the odd abelian Cartan and saturation.

Nonbinary coordinate markings, exchange on this chosen apartment and quotient
root signs remain explicit inputs. The corrected reflections' central defect
must still be removed wherever the source exchange proof needs its precise
root-conjugacy choice. No finite quotient or classification conclusion is
assumed, and this does not complete (14.19) or Theorem D.

Source: DGS, *Groups and Graphs* (1985), (3.6)--(3.7), pp.77--80,
(10.5), pp.155--157, and (14.0)--(14.2), pp.208--211.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (d : ∀ i : Bool, FullCartanReflectionProfile.{uF} h c i)
local notation "n" => fullCartanPathLength d
local notation "hn" => fullCartanPathLength_gt d
local notation "htrans" => fullCartanProfiles_path_transitive d
local notation "hodd" => fullCartanProfiles_path_odd d
/-- The same reflection choices feed the finite quotient with both standard
parabolic equations and the image of the entire original middle subgroup. -/
def fullCartanFiniteQuotient
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n)
    (hsign : ∀ i x, x∈apartmentGroup c (fullCartanPathRoots d) →
  (∀ r∈(fullCartanPathRoots d i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n (x⁻¹*r*x)∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n)) ∨
  (∀ r∈(fullCartanPathRoots d i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n (((fullCartanPathRoots d i).reflection*x)⁻¹*r*((fullCartanPathRoots d i).reflection*x))∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n)))
    : Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
    (recognitionEndpoints (reducedAmalgam L S)) := by
  with_reducible exact (finiteQuotient h c (fullCartanPathRoots d) (fullCartanRoots_normalizes d) (fullCartanRoots_a d) (fullCartanRoots_b d)
    (fullCartanRoots_square d) n hn hodd htrans hexchange hsign)

/-- Both endpoint inclusion squares and the whole middle map are retained. -/
def fullCartanFiniteMarkedIso
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n)
    (hsign : ∀ i x, x∈apartmentGroup c (fullCartanPathRoots d) →
  (∀ r∈(fullCartanPathRoots d i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n (x⁻¹*r*x)∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n)) ∨
  (∀ r∈(fullCartanPathRoots d i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n (((fullCartanPathRoots d i).reflection*x)⁻¹*r*((fullCartanPathRoots d i).reflection*x))∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n)))
    : RankTwoAmalgam.Iso (reducedAmalgam L S)
    (fullCartanFiniteQuotient d hexchange hsign).standardAmalgam := by
  unfold fullCartanFiniteQuotient
  with_reducible exact (finiteMarkedIso h c (fullCartanPathRoots d) (fullCartanRoots_normalizes d) (fullCartanRoots_a d) (fullCartanRoots_b d)
    (fullCartanRoots_square d) n hn hodd htrans hexchange hsign)

/-- The same quotient retains source splitness and saturation. -/
def fullCartanFiniteSplitData
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n)
    (hsign : ∀ i x, x∈apartmentGroup c (fullCartanPathRoots d) →
  (∀ r∈(fullCartanPathRoots d i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n (x⁻¹*r*x)∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n)) ∨
  (∀ r∈(fullCartanPathRoots d i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n (((fullCartanPathRoots d i).reflection*x)⁻¹*r*((fullCartanPathRoots d i).reflection*x))∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots d))) n)))
    : Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
    (fullCartanFiniteQuotient d hexchange hsign).tits := by
  unfold fullCartanFiniteQuotient
  with_reducible exact (finiteSplitData h c (fullCartanPathRoots d) (fullCartanRoots_normalizes d) (fullCartanRoots_a d) (fullCartanRoots_b d)
    (fullCartanRoots_square d) n hn hodd htrans hexchange hsign)

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
