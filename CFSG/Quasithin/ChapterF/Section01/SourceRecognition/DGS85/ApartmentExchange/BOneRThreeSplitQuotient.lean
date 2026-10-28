module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreePathElations
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneFullCartanQuotient

/-!
# The actual marked finite split quotient in the source r=3 branch

The raw class-plane elation argument proves the original whole-Borel root
signs for the same chosen roots, reflections, source relation and quotient
map. Together with the constructed apartment exchange, these discharge both
remaining inputs of the full-Cartan finite quotient constructors.

The resulting quotient retains both kernel-disjoint endpoint embeddings,
exactly two marked simple reflections, both standard-parabolic equations,
the entire original Borel, the original endpoint and middle maps, splitness
and saturation. The equations below expose the literal kernel and maps for
source consumers. The original paired profiles and r=3 source parameters
remain the inputs; the binary and central/r=4 branches are separate.

Source: DGS, *Groups and Graphs* (1985), (3.6)--(3.7), pp.77--80,
and the r=3 branch of (10.5), p.156.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam Configuration
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
local notation "UX" => RankTwoAmalgam.Universal (reducedAmalgam L S)
local notation "T" => cartanApartment A (apartmentGroup c (fullCartanPathRoots ds))
local notation "n" => fullCartanPathLength ds
variable (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)

include hr in
private theorem rThreeExchange : ChosenApartmentExchange (X := UX) (sourceGraph A) T n := by
  rw [(fullCartanProfiles_parameters ds).1.unique hr.1]
  exact fullCartan_source_exchange_of_r_three ds hr

def fullCartanRThreeFiniteQuotient :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient (recognitionEndpoints A) :=
  fullCartanFiniteQuotient ds (by exact rThreeExchange ds hr) (fullCartan_quotient_root_sign_of_r_three ds hr)

def fullCartanRThreeFiniteMarkedIso :
    RankTwoAmalgam.Iso A (fullCartanRThreeFiniteQuotient ds hr).standardAmalgam :=
  fullCartanFiniteMarkedIso ds (by exact rThreeExchange ds hr) (fullCartan_quotient_root_sign_of_r_three ds hr)

def fullCartanRThreeFiniteSplitData :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData (fullCartanRThreeFiniteQuotient ds hr).tits :=
  fullCartanFiniteSplitData ds (by exact rThreeExchange ds hr) (fullCartan_quotient_root_sign_of_r_three ds hr)

@[simp] theorem fullCartanRThreeFiniteQuotient_kernel :
    (fullCartanRThreeFiniteQuotient ds hr).D = kernel A T n := rfl

@[simp] theorem fullCartanRThreeFiniteQuotient_map (x : UX) :
    (fullCartanRThreeFiniteQuotient ds hr).q x = quotientMap A T n x := rfl

theorem fullCartanRThreeFiniteQuotient_borel :
    (originalMiddle A).map (quotientMap A T n) = (fullCartanRThreeFiniteQuotient ds hr).tits.B := by
  have hh := (fullCartanRThreeFiniteQuotient ds hr).borel_image
  change ((Universal.left A).range ⊓ (Universal.right A).range).map (quotientMap A T n) = _ at hh
  rw [Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))] at hh
  exact hh

theorem fullCartanRThreeFiniteQuotient_parabolic (i : Fin 2) :
    (recognitionEndpoints A i).map (quotientMap A T n) =
      (fullCartanRThreeFiniteQuotient ds hr).tits.standardParabolic
        {(fullCartanRThreeFiniteQuotient ds hr).simple i} :=
  (fullCartanRThreeFiniteQuotient ds hr).parabolic_image i

@[simp] theorem fullCartanRThreeFiniteMarkedIso_left_apply
    (x : parabolic L (reducedSylow L S) 0) :
    ((fullCartanRThreeFiniteMarkedIso ds hr).left x).val =
      quotientMap A T n (Universal.left A x) := by
  exact (fullCartanRThreeFiniteQuotient ds hr).markedIso_left_apply
    ((Universal.markedIso (reducedAmalgam L S)
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))).left x)

@[simp] theorem fullCartanRThreeFiniteMarkedIso_right_apply
    (x : parabolic L (reducedSylow L S) 1) :
    ((fullCartanRThreeFiniteMarkedIso ds hr).right x).val =
      quotientMap A T n (Universal.right A x) := by
  exact (fullCartanRThreeFiniteQuotient ds hr).markedIso_right_apply
    ((Universal.markedIso (reducedAmalgam L S)
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))).right x)

@[simp] theorem fullCartanRThreeFiniteMarkedIso_middle_apply
    (x : commonBorel L (reducedSylow L S)) :
    ((fullCartanRThreeFiniteMarkedIso ds hr).middle x).val =
      quotientMap A T n (Universal.left A ((reducedAmalgam L S).left x)) := by
  exact (fullCartanRThreeFiniteQuotient ds hr).markedIso_middle_apply
    ((Universal.markedIso (reducedAmalgam L S)
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))).middle x)

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
