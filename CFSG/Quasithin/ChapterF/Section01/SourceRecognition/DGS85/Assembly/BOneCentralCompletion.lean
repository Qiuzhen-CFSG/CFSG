module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCentralExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCentralGeometry

/-!
# Original natural critical pairs give exchange and marked finite completion

Both original full-Cartan profiles now give exchange at their actual source
length, three or four. Uniqueness and exchange give separation below twice
that length. The same source quotient is finite, injective on both endpoints,
and preserves the entire middle subgroup. Its faithful completion and marked
amalgam isomorphism retain both literal endpoint squares and the middle map.

The original nonsolvable b=1 critical-pair application discharges all profile,
coordinate, root-conjugacy and exchange inputs. In the r=4 branch it retains
the actor center of order q and the natural action on Q/Z. The finite object
here is a geometric completion of the reduced amalgam; identifying its full
Borel image, constructing its Tits system and completing original extension
restoration remain separate source steps.

BOneCentralCompletionConsumers applies this to the unchanged Chapter 12
selected pair. Source: DGS, Groups and Graphs (1985), (10.5), pp.156--157,
(14.10)--(14.15), pp.216--220, and (3.6)--(3.7), pp.77--80.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe u uF
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S
local notation "n" => fullCartanPathLength ds
local notation "ρ" => fullCartanPathRoots ds
local notation "N" => apartmentGroup c ρ
local notation "T" => cartanApartment A N

/-- Both natural source lengths give separation for the same source relation. -/
theorem full_profile_separated :
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
  have hex : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal) (sourceGraph A) T n :=
    full_profile_source_exchange ds
  intro a b hab hd
  exact source_apartment_separated A T n hL hR (fullCartanProfiles_path_transitive ds)
    hline hunique hex (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds)) hab hd

/-- The literal finite quotient preserves both reduced endpoints and the full overlap
also in the r=4 central branch. It is not yet a marked Tits system. -/
theorem full_profile_marked_geometry : HasMarkedGeometricQuotient ds := by
  have hL := inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 0)
  have hR := inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 1)
  have hs : Separated (sourceRelation A T n) (sourceGraph A) (2*n) := full_profile_separated ds
  have hn := fullCartanPathLength_gt ds
  refine ⟨fullCartan_quotient_finite ds,
    kernel_inf_endpoint A T n hL hR hs hn (original_core_eq_bot h),
    quotient_overlap A T n hL hR hs hn,?_,?_⟩
  · exact ⟨quotientCompletion A T n hL hR hs hn (original_core_eq_bot h),rfl,rfl⟩
  · exact ⟨markedIso A T n hL hR hs hn (original_core_eq_bot h),
      fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

/-- The original nonsolvable b=1 critical pair supplies both source branches,
exact root fusion, exchange and the literal marked finite geometric completion.
The r=4 center and Q/Z coordinates remain in its central-root geometry. -/
theorem exchange_geometry_of_critical_bOne
    (h : HypothesisF11 L S)
    (hns : ∀ j : Fin 2, ¬ Group.IsSolvable (parabolic L S j))
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S)=1)
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} h c j,
      ((HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4) ∨
        (HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 ∧
          HasCentralRootGeometry ds)) ∧
      HasMarkedGeometricQuotient ds ∧
      ChosenApartmentExchange (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S))
        (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots ds)))
        (fullCartanPathLength ds) ∧
      ∀ j, ∃ x∈(fullCartanPathRoots ds j).root, orderOf x=2 ∧
        ∃ g∈universalBOneActor h j (ds j).data, g*x*g⁻¹=fullCartanReflections ds j := by
  obtain ⟨ds,he⟩ := marked_geometry_of_critical_bOne_with_central_roots h hns hc hne hb c
  refine ⟨ds,?_,full_profile_marked_geometry ds,full_profile_source_exchange ds,
    root_reflection_conjugacy ds⟩
  exact he.imp And.left id

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
