module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PathRootSigns
public import Theory.GroupTheory.WeakBNPair.RegularTree.PeriodicWeyl

/-!
# Geometric root signs in the actual r=3 finite quotient

The previously constructed source exchange supplies separation below six.
Apply the half-cycle calculation to both literal canonical path roots and
the original chosen reflections. The conclusion uses the same group quotient,
its quotient map, and the stabilizer of its two marked vertex classes.
Explicit equations for the roots and reflections identify the two apartment
constructions without unfolding the earlier full-Cartan profiles.

The full stabilizer of those classes has not yet been identified with the
image of the original whole Borel. Thus this does not supply the Borel-image
root signs required by `fullCartanFiniteQuotient`, and does not claim a split
BN-pair. Borel-image membership for these conjugate roots still needs a source
argument independent of the existing BN-pair-based class-stabilizer theorem.
Nonbinary profiles remain earlier inputs; binary, central and the other source
branches also remain obligations of this source theorem family.

Source: DGS, *Groups and Graphs* (1985), (3.7), printed p.80,
and the r=3 exchange in (14.13), pp.217--218.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S
local notation "n" => fullCartanPathLength ds
local notation "ρ" => fullCartanPathRoots ds
local notation "N" => apartmentGroup c ρ
local notation "T" => cartanApartment A N
local notation "r" => sourceRelation A T n
local notation "q" => quotientMap A T n
local notation "E" => classStabilizer r (apartmentSetoid_invariant (source_action A))
  (base (Universal.cosetFamily A) false) ⊓
  classStabilizer r (apartmentSetoid_invariant (source_action A))
    (base (Universal.cosetFamily A) true)

/-- The same original quotient and chosen reflections satisfy the geometric
root-sign dichotomy in the actual stabilizer of the marked vertex classes.
There is no exchange, natural-coordinate or root-sign premise. The earlier
nonbinary profiles and the genuine r=3 source parameters are retained. -/
theorem fullCartan_quotient_root_class_sign_of_r_three
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)
    (i : Bool) (x : (reducedAmalgam L S).Universal) (hx : x∈N) :
    (∀ u∈(ρ i).root, q (x⁻¹*u*x)∈E) ∨
    (∀ u∈(ρ i).root, q (((ρ i).reflection*x)⁻¹*u*((ρ i).reflection*x))∈E) := by
  let rr := pathRoots h c n (fullCartanPathLength_gt ds) (fullCartanReflections ds)
    (fullCartanReflections_fix ds) (fullCartanReflections_move ds)
    (fullCartanReflections_square ds) (fullCartanReflections_normalize ds)
    (fullCartanProfiles_path_transitive ds) (fullCartanProfiles_thickness ds)
  have hroot (j : Bool) : (ρ j).root=(rr j).root := by
    rw [fullCartanRoots_root]
    exact (pathRoots_root h c n (fullCartanPathLength_gt ds) (fullCartanReflections ds)
      (fullCartanReflections_fix ds) (fullCartanReflections_move ds)
      (fullCartanReflections_square ds) (fullCartanReflections_normalize ds)
      (fullCartanProfiles_path_transitive ds) (fullCartanProfiles_thickness ds) j).symm
  have hN : N=apartmentGroup c rr := by
    unfold apartmentGroup
    apply congrArg Subgroup.closure
    apply congrArg ((cartan c : Set (reducedAmalgam L S).Universal) ∪ ·)
    apply congrArg Set.range
    funext j
    exact (fullCartanRoots_reflection ds j).trans
      (pathRoots_reflection h c n (fullCartanPathLength_gt ds) (fullCartanReflections ds)
        (fullCartanReflections_fix ds) (fullCartanReflections_move ds)
        (fullCartanReflections_square ds) (fullCartanReflections_normalize ds)
        (fullCartanProfiles_path_transitive ds) (fullCartanProfiles_thickness ds) j).symm
  have hsep : Separated (sourceRelation A (cartanApartment A (apartmentGroup c rr)) n)
      (sourceGraph A) (2*n) := by
    rw [←hN]
    exact fullCartan_source_separated_of_r_three ds hr
  have hx' : x∈apartmentGroup c rr := hN ▸ hx
  have hs := pathRoots_class_sign h c n (fullCartanPathLength_gt ds) (fullCartanReflections ds)
    (fullCartanReflections_fix ds) (fullCartanReflections_move ds)
    (fullCartanReflections_square ds) (fullCartanReflections_normalize ds)
    (fullCartanProfiles_path_transitive ds) (fullCartanProfiles_thickness ds) hsep i x hx'
  change (∀ u∈(rr i).root, ∀ j : Bool,
      sourceRelation A (cartanApartment A (apartmentGroup c rr)) n
        ((x⁻¹*u*x) • base (Universal.cosetFamily A) j) (base (Universal.cosetFamily A) j)) ∨
    (∀ u∈(rr i).root, ∀ j : Bool,
      sourceRelation A (cartanApartment A (apartmentGroup c rr)) n
        (((fullCartanReflections ds i*x)⁻¹*u*(fullCartanReflections ds i*x)) •
          base (Universal.cosetFamily A) j) (base (Universal.cosetFamily A) j)) at hs
  rw [←hN,←hroot i] at hs
  have hmem (g : (reducedAmalgam L S).Universal)
      (hg : ∀ j : Bool, r (g • base (Universal.cosetFamily A) j)
        (base (Universal.cosetFamily A) j)) : q g∈E := by
    exact ⟨(mem_classStabilizer r (apartmentSetoid_invariant (source_action A)) g _).mpr (hg false),
      (mem_classStabilizer r (apartmentSetoid_invariant (source_action A)) g _).mpr (hg true)⟩
  rcases hs with hs | hs
  · exact Or.inl (fun u hu => hmem _ (hs u hu))
  · right
    intro u hu
    rw [fullCartanRoots_reflection]
    exact hmem _ (hs u hu)

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
