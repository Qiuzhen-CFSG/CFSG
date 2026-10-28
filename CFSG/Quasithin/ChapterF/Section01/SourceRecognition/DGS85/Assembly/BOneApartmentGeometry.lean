module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneApartment

/-!
# Uniqueness and finiteness for the constructed natural apartment

The two selected involutions normalize the whole source Cartan. Their
reflection orbit is nonbranching in the universal tree. The original Hall
Cartan and odd next-length path fixers then give uniqueness of translated
apartments. Path coverage makes the literal geometric group quotient finite.

These are consequences of the constructed earlier geometry; they do not
assume exchange, root signs or a recognition output. They also do not prove
endpoint injectivity or identify the image of the original whole Borel with
the quotient class stabilizer. Those missing source steps are necessary for
a faithful marked split quotient. BOneApartmentConsumers applies these
results to the actual Chapter 12 pair.

Source: DGS, Groups and Graphs (1985), (3.6)--(3.7), pp.77--80,
and (14.10), pp.215--216.
-/

open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Subgroup.CosetGeometry.RankTwo hiding base

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {c : CompatibleCartans L (reducedSylow L S)}

/-- The chosen whole-Cartan orbit is a nonbranching apartment in the actual universal tree. -/
theorem NaturalApartment.noBranching (d : NaturalApartment L S c) :
    NoBranchingIn (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c d.roots)) :=
  cartanApartment_noBranching (reducedAmalgam L S) (apartmentGroup c d.roots) (cartan c)
    d.roots d.first d.second (reflection_mem_apartmentGroup c d.roots)
    (cartan_le c) (apartmentGroup_normalizes c d.roots d.normalizes) le_rfl d.square
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))

/-- Hall-Cartan uniqueness on the same selected apartment, using the
constructed next-length transitivity and odd path fixers. -/
theorem NaturalApartment.unique (h : HypothesisF11 L S) (d : NaturalApartment L S c) :
    ApartmentsUnique (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c d.roots)) (d.length+1) := by
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  intro a b p hp hlen g k hg hk
  exact cartanApartment_unique (reducedAmalgam L S) (apartmentGroup c d.roots)
    d.roots d.first d.second (reflection_mem_apartmentGroup c d.roots) d.noBranching
    (cartan c) (cartan_le_apartmentGroup c d.roots) (cartan_le c)
    (apartmentGroup_normalizes c d.roots d.normalizes)
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1)) d.length (cartan_hall c) d.odd p hp hlen g k hg hk

/-- The literal geometric quotient is finite. Endpoint injectivity and the
marked split BN-pair still require exchange and the full-Borel root signs. -/
theorem NaturalApartment.quotient_finite (h : HypothesisF11 L S) (d : NaturalApartment L S c) :
    Finite (QuotientGroup (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c d.roots)) d.length) := by
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  exact geometric_quotient_finite (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c d.roots)) d.length
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
    (cartanApartment_base (reducedAmalgam L S) (apartmentGroup c d.roots))
    (cartanApartment_twoNeighbors (reducedAmalgam L S) (apartmentGroup c d.roots)
      d.roots d.first d.second (reflection_mem_apartmentGroup c d.roots)) d.transitive
    (by have := d.length_eq; omega)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
