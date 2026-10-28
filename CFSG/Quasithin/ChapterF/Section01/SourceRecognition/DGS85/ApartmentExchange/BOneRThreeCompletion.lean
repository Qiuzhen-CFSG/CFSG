module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneCenterlessExchange

/-!
# The faithful finite completion in the actual r=3 source branch

The constructed exchange from the original r=3 profiles and odd path fixers
gives separation below six on the same chosen apartment. The quotient of the
possibly infinite universal completion is finite, its kernel meets both
original endpoints trivially, and separation separately proves preservation
of their entire overlap. The resulting faithful completion and marked amalgam
isomorphism retain the literal left, right and whole middle maps.

No natural-coordinate witness, exchange callback or root-sign assumption is
needed for these conclusions. The profiles still supply the nonbinary
whole-Cartan choices. A Tits system, its standard-parabolic equations and
splitness still require the quotient root signs; they are not claimed here.
The binary, central and remaining Chapter 14 source alternatives also remain.

Source: DGS, *Groups and Graphs* (1985), (14.10),(14.13), pp.216--218,
and the finite-quotient construction (3.6)--(3.7), pp.77--80.
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

/-- The actual quotient of the universal completion is finite. This fact
already follows from path coverage, without assuming a finite ambient group. -/
theorem fullCartan_quotient_finite : Finite (QuotientGroup A T n) := by
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  exact geometric_quotient_finite A T n
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
    (cartanApartment_base A N)
    (cartanApartment_twoNeighbors A N ρ (fullCartanRoots_a ds) (fullCartanRoots_b ds)
      (reflection_mem_apartmentGroup c ρ))
    (fullCartanProfiles_path_transitive ds) (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds))

/-- The centerless original profiles imply genuine separation below six,
using the proved exchange on the same chosen apartment. -/
theorem fullCartan_source_separated_of_r_three
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4) :
    Separated (sourceRelation A T n) (sourceGraph A) (2*n) := by
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  have hL := inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 0)
  have hR := inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 1)
  have hnorm := apartmentGroup_normalizes c ρ (fullCartanRoots_normalizes ds)
  have hlift := reflection_mem_apartmentGroup c ρ
  have hline := cartanApartment_noBranching A N (cartan c) ρ (fullCartanRoots_a ds)
    (fullCartanRoots_b ds) hlift (cartan_le c) hnorm le_rfl (fullCartanRoots_square ds) hL hR
  have hunique : ApartmentsUnique (X := (reducedAmalgam L S).Universal) (sourceGraph A) T (n+1) := cartanApartment_unique A N ρ (fullCartanRoots_a ds) (fullCartanRoots_b ds)
    hlift hline (cartan c) (cartan_le_apartmentGroup c ρ) (cartan_le c) hnorm hL hR n
    (cartan_hall c) (fullCartanProfiles_path_odd ds)
  have hex : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal) (sourceGraph A) T n := by
    rw [(fullCartanProfiles_parameters ds).1.unique hr.1]
    exact fullCartan_source_exchange_of_r_three ds hr
  intro a b hab hd
  exact source_apartment_separated A T n hL hR (fullCartanProfiles_path_transitive ds)
    hline hunique hex (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds)) hab hd

/-- Both original endpoint intersections with the same quotient kernel are
trivial; this uses separation and original faithfulness. -/
theorem fullCartan_kernel_inf_endpoints_of_r_three
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4) (i : Bool) :
    kernel A T n ⊓ Universal.cosetFamily A i=⊥ :=
  kernel_inf_endpoint A T n (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
    (fullCartan_source_separated_of_r_three ds hr) (fullCartanPathLength_gt ds)
    (original_core_eq_bot h) i

/-- The full original overlap survives in the finite quotient. This is
proved from separation, separately from kernel-disjointness. -/
theorem fullCartan_quotient_overlap_of_r_three
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4) :
    (leftMap A T n).range ⊓ (rightMap A T n).range=
      (ApartmentExchange.middleMap A T n).range :=
  quotient_overlap A T n (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
    (fullCartan_source_separated_of_r_three ds hr) (fullCartanPathLength_gt ds)

/-- A faithful completion of the original marked amalgam in its constructed
finite quotient, with no coordinate, exchange or root-sign premise. -/
def fullCartanRThreeCompletion
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4) :
    FaithfulCompletion A (G := QuotientGroup A T n) :=
  quotientCompletion A T n (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
    (fullCartan_source_separated_of_r_three ds hr) (fullCartanPathLength_gt ds)
    (original_core_eq_bot h)

/-- The marked amalgam isomorphism keeps both endpoint squares and the whole
middle map. It does not assert a BN-pair before the root signs are proved. -/
def fullCartanRThreeCompletionIso
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4) :
    RankTwoAmalgam.Iso A
      (RankTwoAmalgam.ofSubgroups (leftMap A T n).range
        ((leftMap A T n).range ⊓ (rightMap A T n).range) (rightMap A T n).range
        inf_le_left inf_le_right) :=
  markedIso A T n (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
    (fullCartan_source_separated_of_r_three ds hr) (fullCartanPathLength_gt ds)
    (original_core_eq_bot h)

/-- The left marked map is the restriction of the literal universal quotient. -/
@[simp] theorem fullCartanRThreeCompletionIso_left_apply
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)
    (x : parabolic L (reducedSylow L S) 0) :
    ((fullCartanRThreeCompletionIso ds hr).left x : QuotientGroup A T n)=
      quotientMap A T n (Universal.left A x) := rfl

/-- The right marked map uses the same quotient and the original orientation. -/
@[simp] theorem fullCartanRThreeCompletionIso_right_apply
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)
    (x : parabolic L (reducedSylow L S) 1) :
    ((fullCartanRThreeCompletionIso ds hr).right x : QuotientGroup A T n)=
      quotientMap A T n (Universal.right A x) := rfl

/-- The entire original middle subgroup is carried by that same quotient map. -/
@[simp] theorem fullCartanRThreeCompletionIso_middle_apply
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)
    (x : commonBorel L (reducedSylow L S)) :
    ((fullCartanRThreeCompletionIso ds hr).middle x : QuotientGroup A T n)=
      quotientMap A T n (Universal.left A ((reducedAmalgam L S).left x)) := rfl

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
