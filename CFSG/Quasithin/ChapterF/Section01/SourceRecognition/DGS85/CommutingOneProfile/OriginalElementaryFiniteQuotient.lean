module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryCatalogueConsumers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceWeylParameter

/-!
# The elementary source branch in the literal apartment quotient

The elementary full-Borel quotient constructs its beta catalogue. The
Chapter 11 profile then supplies five-path transitivity and odd five-path
fixers, and the original F.1.1 hypotheses supply tree thickness. Thus the
four-path roots define an actual finite marked apartment quotient and its
split data. The final application feeds that same quotient, its two endpoint
maps and whole Borel map into the marked U₄ comparison.

Only the alpha catalogue and the Chapter 14 Cartans, reflections, exchange,
root-sign alternative remain inputs. The rotation order is proved on
this literal quotient using its periodic apartment. No finite quotient,
split data, beta model or classification profile is assumed.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175,
(14.1)--(14.2), pp.210--211, Theorem D, p.224, and (3.6)--(3.7), pp.77--80.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan

variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original F.1.1 hypotheses supply an exit distinct from either chosen neighbor. -/
theorem original_source_tree_thickness (h : HypothesisF11 L₀ S₀)
    (t : Bool → (reducedAmalgam L₀ S₀).Universal) :
    ∀ i, ∃ z, (sourceGraph (reducedAmalgam L₀ S₀)).Adj
        (Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i) z ∧
      z ≠ Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i) ∧
      z ≠ t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i) := by
  intro i
  let F := Reduction.reducedFamily L₀ S₀
  let A := reducedAmalgam L₀ S₀
  let T := Universal.cosetFamily A
  let c := NoncommutingProfile.bOne_tree_cover h
  let v := c.vertex (Subgroup.CosetGeometry.base T i)
  let := finite_endpoints (Reduction.reduced_triple h)
  have hc := Nat.card_congr
    (Equiv.ofBijective (c.hom.mapNeighborSet (Subgroup.CosetGeometry.base T i)) (c.neighbor_bijective (Subgroup.CosetGeometry.base T i)))
  have hv := card_neighbors_of_indices F
    (fun j => ((F (!j)).subgroupOf (F j)).index) (fun _ => rfl) v
  have hlarge : 3 ≤ Nat.card ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)) := by
    rw [hc]
    change 3 ≤ Nat.card ((graph F).neighborSet v)
    rw [hv]
    exact source_valence_ge_three (Reduction.reduced_triple h)
      (Reduction.reduced_vertex_sylow h) v.type
  let : Finite ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)) :=
    Nat.finite_of_card_ne_zero (by omega)
  have hcard : 2 < ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)).ncard := by
    rw [←Nat.card_coe_set_eq]
    omega
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp hcard
  by_cases hx' : x ≠ Subgroup.CosetGeometry.base T (!i) ∧ x ≠ t i • Subgroup.CosetGeometry.base T (!i)
  · exact ⟨x,hx,hx'⟩
  by_cases hy' : y ≠ Subgroup.CosetGeometry.base T (!i) ∧ y ≠ t i • Subgroup.CosetGeometry.base T (!i)
  · exact ⟨y,hy,hy'⟩
  exact ⟨z,hz,by aesop⟩

variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀)
      (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) false)
      (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀)
        (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) false),
        Z (Reduction.reducedFamily L₀ S₀)
        (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel
      ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) false)).map
          (Reduction.G₀ L₀ S₀).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
          (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) false)).map
            (Reduction.G₀ L₀ S₀).subtype)))
    (helem : letI := FongSeitzBinary.QuadrangleStructure.original_core_normal_in_sylow (L := L₀) (S := reducedSylow L₀ S₀) 1
      IsElementaryAbelian 2 (reducedSylow L₀ S₀ ⧸
        ((parabolic L₀ (reducedSylow L₀ S₀) 1).pCoreIn 2).subgroupOf (reducedSylow L₀ S₀)))
    (cartans : CompatibleCartans L₀ (reducedSylow L₀ S₀))
    (t : Bool → (reducedAmalgam L₀ S₀).Universal)
    (htfix : ∀ i, t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i = Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i)
    (htmove : ∀ i, t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i) ≠ Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i))
    (htsq : ∀ i, t i * t i = 1)
    (htnorm : ∀ i, t i ∈ normalizer (cartan cartans : Set (reducedAmalgam L₀ S₀).Universal))

include h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm

noncomputable def originalElementaryRoots : Bool → LocalRootAction (X := (reducedAmalgam L₀ S₀).Universal)
    (sourceGraph (reducedAmalgam L₀ S₀)) := by
  exact pathRoots h cartans 4 (by decide) t htfix htmove htsq htnorm
    (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
    (original_source_tree_thickness h t)

variable
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L₀ S₀).Universal) (sourceGraph (reducedAmalgam L₀ S₀))
      (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
        (originalElementaryRoots h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm))) 4)
    (hsign : ∀ i x, x ∈ apartmentGroup cartans
        (originalElementaryRoots h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm) →
      (∀ r ∈ (originalElementaryRoots h hc hb hcomm Ma helem cartans t
          htfix htmove htsq htnorm i).root, quotientMap (reducedAmalgam L₀ S₀)
        (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
          (originalElementaryRoots h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm)))
          4 (x⁻¹*r*x) ∈
        (originalMiddle (reducedAmalgam L₀ S₀)).map (quotientMap (reducedAmalgam L₀ S₀)
          (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
            (originalElementaryRoots h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm)))
            4)) ∨
      (∀ r ∈ (originalElementaryRoots h hc hb hcomm Ma helem cartans t
          htfix htmove htsq htnorm i).root, quotientMap (reducedAmalgam L₀ S₀)
        (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
          (originalElementaryRoots h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm)))
          4
          (((originalElementaryRoots h hc hb hcomm Ma helem cartans t
            htfix htmove htsq htnorm i).reflection*x)⁻¹*r*
            ((originalElementaryRoots h hc hb hcomm Ma helem cartans t
              htfix htmove htsq htnorm i).reflection*x)) ∈
        (originalMiddle (reducedAmalgam L₀ S₀)).map (quotientMap (reducedAmalgam L₀ S₀)
          (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
            (originalElementaryRoots h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm)))
            4)))

include h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm hexchange hsign

/-- The actual finite marked quotient obtained from the elementary source roots. -/
def originalElementaryFiniteQuotient :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
      (recognitionEndpoints (reducedAmalgam L₀ S₀)) := by
  exact finiteQuotient h cartans
    (originalElementaryRoots h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm)
    (ReducedCartan.pathRoots_normalizes h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_a h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_b h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_square h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    4 (by decide)
    (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).2
    (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
    hexchange hsign

/-- The quotient retains both original endpoint maps and the full Borel map. -/
def originalElementaryFiniteMarkedIso :
    RankTwoAmalgam.Iso (reducedAmalgam L₀ S₀) (originalElementaryFiniteQuotient h hc hb hcomm Ma helem
      cartans t htfix htmove htsq htnorm hexchange hsign).standardAmalgam := by
  unfold originalElementaryFiniteQuotient
  exact finiteMarkedIso h cartans
    (originalElementaryRoots h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm)
    (ReducedCartan.pathRoots_normalizes h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_a h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_b h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_square h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    4 (by decide)
    (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).2
    (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
    hexchange hsign

/-- The same quotient carries the original split factorization and saturation. -/
def originalElementaryFiniteSplitData :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
      (originalElementaryFiniteQuotient h hc hb hcomm Ma helem cartans t htfix htmove
        htsq htnorm hexchange hsign).tits := by
  unfold originalElementaryFiniteQuotient
  exact finiteSplitData h cartans
    (originalElementaryRoots h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm)
    (ReducedCartan.pathRoots_normalizes h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_a h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_b h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_square h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    4 (by decide)
    (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).2
    (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
    hexchange hsign

/-- The marked Weyl parameter is the actual source value four. -/
theorem originalElementaryFiniteRotationOrder :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates.rotationOrder
      (originalElementaryFiniteQuotient h hc hb hcomm Ma helem cartans t
        htfix htmove htsq htnorm hexchange hsign) = 4 := by
  unfold originalElementaryFiniteQuotient
  exact finiteQuotient_simple_product_order h cartans
    (originalElementaryRoots h hc hb hcomm Ma helem cartans t htfix htmove htsq htnorm)
    (ReducedCartan.pathRoots_normalizes h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_a h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_b h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    (ReducedCartan.pathRoots_square h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
      (original_source_tree_thickness h t))
    4 (by decide)
    (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).2
    (original_elementary_tree_path_profile_of_alpha_model h hc hb hcomm Ma helem).1
    hexchange hsign

/-- The literal constructed quotient and its split data discharge those
premises of the elementary marked comparison. The rotation order is also
proved for this same quotient, retaining both endpoints and the full Borel. -/
theorem originalElementaryFiniteComparison
    :
    ∃ (m : ℕ) (hm : 0 < m), Nonempty (RankTwoAmalgam.Iso (reducedAmalgam L₀ S₀)
      (UnitaryFourNative.amalgam m hm false)) := by
  exact original_elementary_reduced_comparison_of_alpha_model h hc hb hcomm Ma helem
    (originalElementaryFiniteQuotient h hc hb hcomm Ma helem cartans t
      htfix htmove htsq htnorm hexchange hsign)
    (originalElementaryFiniteMarkedIso h hc hb hcomm Ma helem cartans t
      htfix htmove htsq htnorm hexchange hsign)
    (originalElementaryFiniteSplitData h hc hb hcomm Ma helem cartans t
      htfix htmove htsq htnorm hexchange hsign)
    (originalElementaryFiniteRotationOrder h hc hb hcomm Ma helem cartans t
      htfix htmove htsq htnorm hexchange hsign)

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
