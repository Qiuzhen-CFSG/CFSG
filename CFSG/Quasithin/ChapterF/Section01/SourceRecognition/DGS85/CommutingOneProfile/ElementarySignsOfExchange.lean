module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalElementaryFiniteQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceWeylParameter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryInteriorStars
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FourPathRootImages

/-!
# Elementary whole-Borel root signs, including the binary case

The elementary source supplies both endpoint catalogues and fixation of
interior stars. Its five-path transitivity and odd fixers make the apartment
quotient a thick generalized quadrangle once exchange is available.
Periodic root rigidity then proves both whole-Borel signs without any
nonbinary assumption. The literal marked U4 comparison uses these signs on
the same quotient, with the original Borel and both endpoint inclusions.

This removes the sign obligation also at beta field order two. Choosing the
binary reflections and proving their apartment exchange remain source duties.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175,
(14.1)--(14.2), pp.210--211, and (3.6)--(3.7), pp.77--80.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

include h hc hb hcomm helem


variable (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i*t i=1)
    (htnorm : ∀ i, t i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

include c t htfix htmove htsq htnorm
variable (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
    (sourceGraph (reducedAmalgam L S))
    (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4)
include hexchange

/-- Both signs of the original four-path radicals lie in the whole original
Borel image on the literal apartment quotient. -/
theorem original_elementary_root_signs_of_exchange :
    ∀ i x, x∈reflectionGroup c t →
      (∀ r∈((pathRoots h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm (original_elementary_tree_path_profile h hc hb hcomm (original_borel_elementary_alpha_model h hc hb helem) (original_borel_elementary_beta_model h helem) helem).1 (original_source_tree_thickness h t)) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4
        (x⁻¹*r*x)∈(originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4)) ∨
      (∀ r∈((pathRoots h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm (original_elementary_tree_path_profile h hc hb hcomm (original_borel_elementary_alpha_model h hc hb helem) (original_borel_elementary_beta_model h helem) helem).1 (original_source_tree_thickness h t)) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4
        ((t i*x)⁻¹*r*(t i*x))∈(originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4)) := by
  intro i x hx
  let AA := reducedAmalgam L S
  let roots := pathRoots h c 4 (by decide) t htfix htmove htsq htnorm (original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem).1 (original_source_tree_thickness h t)
  let NN := apartmentGroup c roots
  let TT := cartanApartment AA NN
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  have htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 5 := (original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem).1
  have hodd : ∀ {a b : SourceVertex (reducedAmalgam L S)}
      (p : (sourceGraph (reducedAmalgam L S)).Walk a b), p.IsPath → p.length=5 →
      Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) := (original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem).2
  have hthick := original_source_tree_thickness h t
  have ha := pathRoots_a h c 4 (by decide) t htfix htmove htsq htnorm htrans hthick
  have hb' := pathRoots_b h c 4 (by decide) t htfix htmove htsq htnorm htrans hthick
  have hlifts := reflection_mem_apartmentGroup c roots
  have hnorm := apartmentGroup_normalizes c roots
    (pathRoots_normalizes h c 4 (by decide) t htfix htmove htsq htnorm htrans hthick)
  have hinv := pathRoots_square h c 4 (by decide) t htfix htmove htsq htnorm htrans hthick
  have hL := inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 0)
  have hR := inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 1)
  let tree := Universal.cosetGraph_isTree AA hL hR
  have hdeg := cartanApartment_twoNeighbors AA NN roots ha hb' hlifts
  have hline := cartanApartment_noBranching AA NN (cartan c) roots ha hb' hlifts
    (cartan_le c) hnorm le_rfl hinv hL hR
  have hunique : ApartmentsUnique (X := AA.Universal) (sourceGraph AA) TT 5 :=
    cartanApartment_unique AA NN roots ha hb' hlifts hline (cartan c)
    (cartan_le_apartmentGroup c roots) (cartan_le c) hnorm hL hR 4 (cartan_hall c) hodd
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
    rw [card_neighbors_of_indices (reducedFamily L S)
      (fun j => ((reducedFamily L S (!j)).subgroupOf (reducedFamily L S j)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) _
  exact four_pathRoots_global_sign_of_root_rigidity h c 4 (by decide) t htfix htmove htsq htnorm
    htrans hthick hsep hlift rfl
    (original_elementary_pathRoot_fixes_interior_stars h hc hb helem)
    (four_class_root_rigidity AA TT hL hR hval hsep hlift hdeg hcover) i x hx

/-- The literal U4 comparison for every positive field degree, with the
whole-Borel root signs proved. Reflections and exchange remain explicit. -/
theorem original_elementary_comparison_of_exchange :
    ∃ (m : ℕ) (hm : 0<m), Nonempty (Iso A (UnitaryFourNative.amalgam m hm false)) := by
  let := FongSeitzBinary.QuadrangleStructure.original_core_normal_in_sylow
    (L := L) (S := reducedSylow L S) 1
  have he : IsElementaryAbelian 2 (reducedSylow L S ⧸
      ((parabolic L (reducedSylow L S) 1).pCoreIn 2).subgroupOf (reducedSylow L S)) := by
    have hq : (Q F (base F true)).map (G₀).subtype =
        (parabolic L (reducedSylow L S) 1).pCoreIn 2 :=
      (reduced_base_Q_map h true).trans (reduced_parabolic_core h 1).symm
    have he := helem
    rw [hq] at he
    obtain ⟨hn,he⟩ := he
    exact he
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have hsign := original_elementary_root_signs_of_exchange h hc hb hcomm helem
    c t htfix htmove htsq htnorm hexchange
  let quot := pathFiniteQuotient h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm
    hpath.1 (original_source_tree_thickness h t) hpath.2 hexchange hsign
  exact original_elementary_reduced_comparison_of_source h hc hb hcomm he quot
    (pathFiniteMarkedIso h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm
      hpath.1 (original_source_tree_thickness h t) hpath.2 hexchange hsign)
    (pathFiniteSplitData h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm
      hpath.1 (original_source_tree_thickness h t) hpath.2 hexchange hsign)
    (pathFiniteQuotient_simple_product_order h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm
      hpath.1 (original_source_tree_thickness h t) hpath.2 hexchange hsign)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
