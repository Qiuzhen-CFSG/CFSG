module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceInteriorStars
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FourPathRootImages
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FullUnitaryFiniteComparison

/-!
# Whole-Borel root signs for the original unitary branch

The marked PSU3 or SU3 source supplies the five-path transitivity and odd
fixers. Given the retained apartment exchange, its class graph is a thick
generalized quadrangle. The actual path radicals fix its interior stars;
matching one exit and root rigidity identify the periodically shifted
root images. Both root signs therefore lie in the image of the entire
original Borel on this same quotient.

Apply these proved signs to the finite split quotient and the all-fields
marked U5 recognition, preserving both endpoint maps and the full Borel.
The alpha catalogue, beta marking, reflections and exchange are retained;
this does not assert their construction or full source classification.
Source: DGS, Groups and Graphs (1985), (11.8), pp.175--177,
(14.1)--(14.2), pp.210--211, (3.6)--(3.7), pp.77--80, and Theorem D, p.224.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
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
open Reduction

variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}

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
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU
        ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
          (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)).map
            (Reduction.G₀ L₀ S₀).subtype ⧸
          pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
            (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)).map
              (Reduction.G₀ L₀ S₀).subtype)) 3 (2^m) ∨
      IsSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)).map
          (Reduction.G₀ L₀ S₀).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
          (Subgroup.CosetGeometry.base (Reduction.reducedFamily L₀ S₀) true)).map
            (Reduction.G₀ L₀ S₀).subtype)) 3 (2^m))
    (cartans : CompatibleCartans L₀ (reducedSylow L₀ S₀))
    (t : Bool → (reducedAmalgam L₀ S₀).Universal)
    (htfix : ∀ i, t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i = Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i)
    (htmove : ∀ i, t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i) ≠ Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i))
    (htsq : ∀ i, t i * t i = 1)
    (htnorm : ∀ i, t i ∈ normalizer (cartan cartans : Set (reducedAmalgam L₀ S₀).Universal))

include h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm

variable
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L₀ S₀).Universal) (sourceGraph (reducedAmalgam L₀ S₀))
      (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
        (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm))) 4)

include hexchange

/-- The original unitary root signs on the literal quotient, with both
unitary covers and every positive field degree retained. -/
theorem original_unitary_root_signs_of_exchange : ∀ i x, x ∈ apartmentGroup cartans
        (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm) →
      (∀ r ∈ (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
          htfix htmove htsq htnorm i).root, quotientMap (reducedAmalgam L₀ S₀)
        (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
          (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
          4 (x⁻¹*r*x) ∈
        (originalMiddle (reducedAmalgam L₀ S₀)).map (quotientMap (reducedAmalgam L₀ S₀)
          (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
            (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
            4)) ∨
      (∀ r ∈ (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
          htfix htmove htsq htnorm i).root, quotientMap (reducedAmalgam L₀ S₀)
        (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
          (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
          4
          (((originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
            htfix htmove htsq htnorm i).reflection*x)⁻¹*r*
            ((originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
              htfix htmove htsq htnorm i).reflection*x)) ∈
        (originalMiddle (reducedAmalgam L₀ S₀)).map (quotientMap (reducedAmalgam L₀ S₀)
          (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
            (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
            4)) := by
  intro i x hx
  let AA := reducedAmalgam L₀ S₀
  let roots := originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm
  let NN := apartmentGroup cartans roots
  let TT := cartanApartment AA NN
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  have htrans : BasedPathTransitive (X := AA.Universal) (sourceGraph AA) 5 := (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
  have hodd : ∀ {a b : SourceVertex AA} (p : (sourceGraph AA).Walk a b),
      p.IsPath → p.length = 5 → Odd (Nat.card (pathFixer (X := AA.Universal) p)) := (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).2
  have hthick := original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t
  have ha := pathRoots_a h cartans 4 (by decide) t htfix htmove htsq htnorm htrans hthick
  have hb' := pathRoots_b h cartans 4 (by decide) t htfix htmove htsq htnorm htrans hthick
  have hlifts := reflection_mem_apartmentGroup cartans roots
  have hnorm := apartmentGroup_normalizes cartans roots
    (pathRoots_normalizes h cartans 4 (by decide) t htfix htmove htsq htnorm htrans hthick)
  have hinv := pathRoots_square h cartans 4 (by decide) t htfix htmove htsq htnorm htrans hthick
  have hL := inclusion_injective (commonBorel_le_parabolic (L := L₀) (S := reducedSylow L₀ S₀) 0)
  have hR := inclusion_injective (commonBorel_le_parabolic (L := L₀) (S := reducedSylow L₀ S₀) 1)
  let tree := Universal.cosetGraph_isTree AA hL hR
  have hdeg := cartanApartment_twoNeighbors AA NN roots ha hb' hlifts
  have hline := cartanApartment_noBranching AA NN (cartan cartans) roots ha hb' hlifts
    (cartan_le cartans) hnorm le_rfl hinv hL hR
  have hunique : ApartmentsUnique (X := AA.Universal) (sourceGraph AA) TT 5 :=
    cartanApartment_unique AA NN roots ha hb' hlifts hline (cartan cartans)
    (cartan_le_apartmentGroup cartans roots) (cartan_le cartans) hnorm hL hR 4 (cartan_hall cartans) hodd
  have hsep : Separated (sourceRelation AA TT 4) (sourceGraph AA) 8 :=
    source_apartment_separated AA TT 4 hL hR htrans hline hunique hexchange (by decide)
  have hlift : NeighborLifting (sourceGraph AA) (sourceRelation AA TT 4) := by
    intro a b z hab hbz
    exact apartmentSetoid_neighbor_lift 4 (by decide) tree (source_action AA) hdeg htrans
      (apartmentExchangeMoves_of_chosen (source_action AA) hexchange) hab hbz
  have hcover : ApartmentsCover (X := AA.Universal) (sourceGraph AA) TT 5 :=
    source_apartments_cover AA TT 4 hL hR (cartanApartment_base AA NN) hdeg htrans
  have hval (v : SourceVertex AA) : 3 ≤ Nat.card ((sourceGraph AA).neighborSet v) := by
    let cov := NoncommutingProfile.bOne_tree_cover h
    rw [Nat.card_congr (Equiv.ofBijective _ (cov.neighbor_bijective v))]
    rw [card_neighbors_of_indices (reducedFamily L₀ S₀)
      (fun j => ((reducedFamily L₀ S₀ (!j)).subgroupOf (reducedFamily L₀ S₀ j)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) _
  have models (j : Bool) : IsRankOneModel
      ((graphLocalGroup (reducedFamily L₀ S₀) (Subgroup.CosetGeometry.base (reducedFamily L₀ S₀) j)).map
        (Reduction.G₀ L₀ S₀).subtype ⧸ pCore 2
          ((graphLocalGroup (reducedFamily L₀ S₀) (Subgroup.CosetGeometry.base (reducedFamily L₀ S₀) j)).map
            (Reduction.G₀ L₀ S₀).subtype)) := by
    cases j
    · exact Ma
    · exact mark.elim (.projective_unitary m hm) (.special_unitary m hm)
  exact four_pathRoots_global_sign_of_root_rigidity h cartans 4 (by decide) t htfix htmove htsq htnorm
    htrans hthick hsep hlift rfl
    (original_pathRoot_fixes_interior_stars_of_models h models)
    (four_class_root_rigidity AA TT hL hR hval hsep hlift hdeg hcover) i x hx

/-- The same finite marked comparison with the root-sign premise discharged.
All three comparison maps use the original quotient representatives. -/
theorem originalUnitaryFiniteComparisonOfExchange :
    Nonempty (FongSeitzBinary.UnitarySource.Combined.FiveComparison
      (originalUnitaryFiniteQuotient h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm hexchange
        (original_unitary_root_signs_of_exchange h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm hexchange))
      (originalUnitaryFiniteMarkedIso h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm hexchange
        (original_unitary_root_signs_of_exchange h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm hexchange)) m false) :=
  originalUnitaryFiniteComparisonFromMarking h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm hexchange
    (original_unitary_root_signs_of_exchange h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm hexchange)

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
