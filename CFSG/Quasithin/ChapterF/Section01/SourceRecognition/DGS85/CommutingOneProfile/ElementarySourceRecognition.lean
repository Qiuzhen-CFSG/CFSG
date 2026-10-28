module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementarySourceExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryInteriorStars
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FourPathRootImages

/-!
# Original nonbinary elementary root signs and marked recognition

Exchange and odd five-path fixers make the literal apartment class graph a
thick generalized quadrangle. The actual four-path radicals fix the interior
stars; matching one exit and geometric rigidity identify their periodic
quotient images. Thus the half-apartment signs belong to the WHOLE original
Borel image. No sign, exchange or local-kernel premise remains.

Apply these signs to the same marked finite split quotient, retaining both
endpoint maps and its order-four Weyl rotation. The resulting reduced
amalgam is the marked U4 amalgam. The binary and nonelementary branches and
restoration of the original pair remain separate obligations of 11.7/11.8.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175,
(3.6)--(3.7), pp.77--80, and Theorem D, p.224.
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
variable (hnb : ¬ ClassicalGroup.IsPSL
  ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
    (Reduction.G₀ L S).subtype ⧸ pCore 2
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype)) 2 2)
include hnb

/-- Both signs of the original four-path radicals lie in the whole original
Borel image on the literal apartment quotient. -/
theorem original_elementary_nonbinary_root_signs :
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
  have hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4 := by
    exact original_elementary_nonbinary_apartment_exchange_of_source
      h hc hb hcomm helem c t htfix htmove htsq htnorm hnb
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

/-- The marked U4 comparison with all nonbinary elementary source inputs proved. -/
theorem original_elementary_nonbinary_comparison_with_reflections :
    ∃ (m : ℕ) (hm : 0<m), Nonempty (Iso A (UnitaryFourNative.amalgam m hm false)) := by
  exact original_elementary_nonbinary_comparison_of_signs h hc hb hcomm helem
    c t htfix htmove htsq htnorm hnb
    (original_elementary_nonbinary_root_signs h hc hb hcomm helem
      c t htfix htmove htsq htnorm hnb)

omit c t htfix htmove htsq htnorm in
/-- The original nonbinary elementary hypotheses construct the full marked
reduced U4 amalgam comparison, including the full Borel map. -/
theorem original_elementary_nonbinary_reduced_comparison :
    ∃ (m : ℕ) (hm : 0<m), Nonempty (Iso A (UnitaryFourNative.amalgam m hm false)) := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb (chosenCartans h)
  exact original_elementary_nonbinary_comparison_with_reflections h hc hb hcomm helem
    (chosenCartans h) t htfix htmove htsq htnorm hnb

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
