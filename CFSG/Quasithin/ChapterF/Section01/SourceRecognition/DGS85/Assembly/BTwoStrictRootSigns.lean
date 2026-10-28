module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictSourceQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictPathInteriorStars
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixPathRootImages
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixClassGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource

/-!
# The strict source root signs from apartment exchange

The original strict hypotheses supply linear interior-star fixation, seven-path
transitivity and odd seven-path fixers. Apartment exchange supplies separation
and neighbor lifting. The raw quotient is therefore a thick generalized
hexagon; root rigidity identifies the global images of periodic path roots.
The half-apartment argument proves the whole original Borel sign alternative.

Thus the source finite quotient, both endpoint inclusion squares and split data
require only the remaining exchange input. Neither root signs nor any local or
global kernel comparison is assumed.
Source: DGS, *Groups and Graphs* (1985), (3.6)--(3.7), pp.77--80;
(10.10), p.164; (14.1)--(14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2) (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
  (c : CompatibleCartans L (reducedSylow L S))
  (t : Bool → (reducedAmalgam L S).Universal)
  (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
    base (Universal.cosetFamily (reducedAmalgam L S)) i)
  (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
    base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
  (htsq : ∀ i, t i * t i = 1)
  (htnorm : ∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal))


variable (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S))
  (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 6)

include hexchange in
include hexchange in
/-- The literal strict six-path radicals satisfy both global Borel signs. -/
theorem strict_root_signs_of_exchange (i : Bool) (x : (reducedAmalgam L S).Universal)
    (hx : x ∈ reflectionGroup c t) :
    (∀ r ∈ (strictPathRoots h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm i).root,
      quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
        (reflectionGroup c t)) 6 (x⁻¹*r*x) ∈ (originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
            (reflectionGroup c t)) 6)) ∨
    (∀ r ∈ (strictPathRoots h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm i).root,
      quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
        (reflectionGroup c t)) 6 ((t i*x)⁻¹*r*(t i*x)) ∈
          (originalMiddle (reducedAmalgam L S)).map
            (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
              (reflectionGroup c t)) 6)) := by
  let A := reducedAmalgam L S
  let ρ := strictPathRoots h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm
  let N := apartmentGroup c ρ
  let T := cartanApartment A N
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  have htrans := @strict_tree_path_transitive_source G _ L S u h hc hne hb hβu hns n hlinear
  have hodd := @strict_tree_path_fixers_odd_source G _ L S u h hc hne hb hβu hns n hlinear
  have hthick := strict_path_thickness_source h t htfix htmove
  have ha := pathRoots_a h c 6 (by decide) t htfix htmove htsq htnorm htrans hthick
  have hb' := pathRoots_b h c 6 (by decide) t htfix htmove htsq htnorm htrans hthick
  have hlifts := reflection_mem_apartmentGroup c ρ
  have hnorm := apartmentGroup_normalizes c ρ
    (pathRoots_normalizes h c 6 (by decide) t htfix htmove htsq htnorm htrans hthick)
  have hinv := pathRoots_square h c 6 (by decide) t htfix htmove htsq htnorm htrans hthick
  have hL := inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 0)
  have hR := inclusion_injective (commonBorel_le_parabolic (L := L) (S := reducedSylow L S) 1)
  let tree := Universal.cosetGraph_isTree A hL hR
  have hdeg := cartanApartment_twoNeighbors A N ρ ha hb' hlifts
  have hline := cartanApartment_noBranching A N (cartan c) ρ ha hb' hlifts
    (cartan_le c) hnorm le_rfl hinv hL hR
  have hunique : ApartmentsUnique (X := A.Universal) (sourceGraph A) T 7 :=
    cartanApartment_unique A N ρ ha hb' hlifts hline (cartan c)
    (cartan_le_apartmentGroup c ρ) (cartan_le c) hnorm hL hR 6 (cartan_hall c) hodd
  have hsep : Separated (sourceRelation A T 6) (sourceGraph A) 12 :=
    source_apartment_separated A T 6 hL hR htrans hline hunique hexchange (by decide)
  have hlift : NeighborLifting (sourceGraph A) (sourceRelation A T 6) := by
    intro a b z hab hbz
    exact apartmentSetoid_neighbor_lift 6 (by decide) tree (source_action A) hdeg htrans
      (apartmentExchangeMoves_of_chosen (source_action A) hexchange) hab hbz
  have hcover : ApartmentsCover (X := A.Universal) (sourceGraph A) T 7 :=
    source_apartments_cover A T 6 hL hR (cartanApartment_base A N) hdeg htrans
  have hval (v : SourceVertex A) : 3 ≤ Nat.card ((sourceGraph A).neighborSet v) := by
    let cov := NoncommutingProfile.bOne_tree_cover h
    rw [Nat.card_congr (Equiv.ofBijective _ (cov.neighbor_bijective v))]
    rw [card_neighbors_of_indices (reducedFamily L S)
      (fun j => ((reducedFamily L S (!j)).subgroupOf (reducedFamily L S j)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) _
  exact pathRoots_global_sign_of_root_rigidity h c 6 (by decide) t htfix htmove htsq htnorm
    htrans hthick hsep hlift rfl
    (original_bTwo_strict_pathRoot_fixes_interior_stars h hc hne hb hβu hns hlinear)
    (six_class_root_rigidity A T hL hR hval hsep hlift hdeg hcover) i x hx

/-- Source-selected reflections satisfy the named original root-sign contract. -/
theorem strict_source_root_signs_of_exchange
    (hexchange : StrictSourceExchange h hc hne hb hβu hns hlinear) :
    StrictSourceRootSigns h hc hne hb hβu hns hlinear := by
  let d := strictSourceReflections h hc hne hb hβu hns hlinear
  exact strict_root_signs_of_exchange h hc hne hb hβu hns hlinear (chosenCartans h)
    d.t d.fixes d.moves d.square d.normalizes hexchange

/-- The literal finite marked quotient with root signs discharged. -/
def strictSourceFiniteQuotientOfExchange
    (hexchange : StrictSourceExchange h hc hne hb hβu hns hlinear) :
    MarkedQuotient (recognitionEndpoints (reducedAmalgam L S)) :=
  strictSourceFiniteQuotient h hc hne hb hβu hns hlinear hexchange
    (strict_source_root_signs_of_exchange h hc hne hb hβu hns hlinear hexchange)

/-- Both original endpoint squares and the whole middle map after sign discharge. -/
def strictSourceFiniteMarkedIsoOfExchange
    (hexchange : StrictSourceExchange h hc hne hb hβu hns hlinear) :
    Iso (reducedAmalgam L S)
      (strictSourceFiniteQuotientOfExchange h hc hne hb hβu hns hlinear hexchange).standardAmalgam :=
  strictSourceFiniteMarkedIso h hc hne hb hβu hns hlinear hexchange
    (strict_source_root_signs_of_exchange h hc hne hb hβu hns hlinear hexchange)

/-- Split data on the same source quotient after sign discharge. -/
def strictSourceFiniteSplitDataOfExchange
    (hexchange : StrictSourceExchange h hc hne hb hβu hns hlinear) :
    SplitData (strictSourceFiniteQuotientOfExchange h hc hne hb hβu hns hlinear hexchange).tits :=
  strictSourceFiniteSplitData h hc hne hb hβu hns hlinear hexchange
    (strict_source_root_signs_of_exchange h hc hne hb hβu hns hlinear hexchange)

/-- The original strict quotient has Weyl rotation order six after sign discharge. -/
theorem strictSourceFiniteQuotientOfExchange_rotation
    (hexchange : StrictSourceExchange h hc hne hb hβu hns hlinear) :
    rotationOrder (strictSourceFiniteQuotientOfExchange h hc hne hb hβu hns hlinear hexchange) = 6 :=
  strictSourceFiniteQuotient_rotation h hc hne hb hβu hns hlinear hexchange
    (strict_source_root_signs_of_exchange h hc hne hb hβu hns hlinear hexchange)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
