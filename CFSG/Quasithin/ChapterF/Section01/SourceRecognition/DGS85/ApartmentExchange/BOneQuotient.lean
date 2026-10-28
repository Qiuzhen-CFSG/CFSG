module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneReflectionPaths

/-!
# The marked finite quotient from the b=1 actor reflections

Use the actual actor-selected involutions and their constructed length-three
path roots on the universal reduced amalgam. The genuine Chapter 10 profiles
discharge four-path transitivity, odd four-path stabilizers and thickness.
The finite quotient therefore uses these same choices and retains both
standard-parabolic equations, the image of the whole original Borel, both
endpoint inclusion squares, and source splitness with saturation.

The coordinate markings in `ActorReflectionProfile`, the chosen-apartment
exchange condition and quotient root signs remain explicit. Discharging them
and treating the other Chapter 14 branches are still required for (14.19)
and Theorem D. This application does not assume a finite quotient or a
classification result.

Source: DGS, *Groups and Graphs* (1985), (3.6)--(3.7), pp.77--80, (10.5),
pp.155--157, and (14.1)--(14.2), pp.210--211.
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
variable (d : ∀ i : Bool, ActorReflectionProfile.{uF} h c i)
local notation "n" => (3 : ℕ)
local notation "hn" => (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
local notation "htrans" => actorProfiles_path_transitive d
local notation "hodd" => actorProfiles_path_odd d
variable (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (cartanApartment (reducedAmalgam L S) (apartmentGroup c (actorReflectionPathRoots d))) n)
variable (hsign : ∀ i x, x∈apartmentGroup c (actorReflectionPathRoots d) →
  (∀ r∈(actorReflectionPathRoots d i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (actorReflectionPathRoots d))) n (x⁻¹*r*x)∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c (actorReflectionPathRoots d))) n)) ∨
  (∀ r∈(actorReflectionPathRoots d i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (actorReflectionPathRoots d))) n (((actorReflectionPathRoots d i).reflection*x)⁻¹*r*((actorReflectionPathRoots d i).reflection*x))∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c (actorReflectionPathRoots d))) n)))

/-- The same reflection choices feed the finite quotient with both standard
parabolic equations and the image of the entire original middle subgroup. -/
def actorFiniteQuotient : Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
    (recognitionEndpoints (reducedAmalgam L S)) :=
  finiteQuotient h c (actorReflectionPathRoots d) (actorRoots_normalizes d) (actorRoots_a d) (actorRoots_b d)
    (actorRoots_square d) n hn hodd htrans hexchange hsign

/-- Both endpoint inclusion squares and the whole middle map are retained. -/
def actorFiniteMarkedIso : RankTwoAmalgam.Iso (reducedAmalgam L S)
    (actorFiniteQuotient d hexchange hsign).standardAmalgam :=
  finiteMarkedIso h c (actorReflectionPathRoots d) (actorRoots_normalizes d) (actorRoots_a d) (actorRoots_b d)
    (actorRoots_square d) n hn hodd htrans hexchange hsign

/-- The same quotient retains source splitness and saturation. -/
def actorFiniteSplitData : Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
    (actorFiniteQuotient d hexchange hsign).tits :=
  finiteSplitData h c (actorReflectionPathRoots d) (actorRoots_normalizes d) (actorRoots_a d) (actorRoots_b d)
    (actorRoots_square d) n hn hodd htrans hexchange hsign

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
