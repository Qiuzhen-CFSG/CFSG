module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictRootSigns
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearHexagonRecognition

/-!
# Linear hexagon comparison from the actual path geometry

The two original linear factors give interior-star fixation directly, including
solvable binary endpoints. Seven-path transitivity, odd seven-path fixers, and
exchange then give the whole-Borel root signs and the same marked split finite
quotient. Unequal field orders identify its literal triality amalgam.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open Reduction OriginalExtension Assembly.BTwoSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S)
    {k : Bool → Type*} [∀ i, Field (k i)] [∀ i, Finite (k i)] [∀ i, CharP (k i) 2]
    (μ : ∀ i : Bool, (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k i))
    (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i * t i = 1)
    (htnorm : ∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal))
    (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7)
    (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length = 7 → Odd (Nat.card
        (pathFixer (X := (reducedAmalgam L S).Universal) p)))
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 6)
include h μ c t htfix htmove htsq htnorm htrans hodd hexchange

private theorem linear_six_root_signs (i : Bool) (x : (reducedAmalgam L S).Universal)
    (hx : x ∈ reflectionGroup c t) :
    let ρ := pathRoots h c 6 (by decide) t htfix htmove htsq htnorm htrans
      (strict_path_thickness_source h t htfix htmove)
    (∀ r ∈ (ρ i).root,
      quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
        (reflectionGroup c t)) 6 (x⁻¹*r*x) ∈ (originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
            (reflectionGroup c t)) 6)) ∨
    (∀ r ∈ (ρ i).root,
      quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
        (reflectionGroup c t)) 6 ((t i*x)⁻¹*r*(t i*x)) ∈
          (originalMiddle (reducedAmalgam L S)).map
            (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
              (reflectionGroup c t)) 6)) := by
  let A := reducedAmalgam L S
  have hthick := strict_path_thickness_source h t htfix htmove
  let ρ := pathRoots h c 6 (by decide) t htfix htmove htsq htnorm htrans hthick
  let N := apartmentGroup c ρ
  let T := cartanApartment A N
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
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
    (linear_pathRoot_fixes_interior_stars h μ)
    (six_class_root_rigidity A T hL hR hval hsep hlift hdeg hcover) i x hx

/-- Unequal original linear factors on the seven-path source give the actual
triality comparison from exchange, including a binary solvable endpoint. -/
theorem unequal_linear_comparison_of_exchange
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hsmall : Nat.card (k false) = 2^a) (hlarge : Nat.card (k true) = 2^b) :
    b = 3*a ∧ Nonempty (Iso
      (Chapter6.Source.RankOneGeneric.Global.sourceParabolicAmalgam L (reducedSylow L S))
      (FongSeitzBinary.TrialityPresentation.flagAmalgam a ha 1)) := by
  let hthick := strict_path_thickness_source h t htfix htmove
  let hsign := linear_six_root_signs h μ c t htfix htmove htsq htnorm htrans hodd hexchange
  let Q := pathFiniteQuotient h c 6 (by decide) t htfix htmove htsq htnorm htrans
    hthick hodd hexchange hsign
  let mark := pathFiniteMarkedIso h c 6 (by decide) t htfix htmove htsq htnorm htrans
    hthick hodd hexchange hsign
  let split := pathFiniteSplitData h c 6 (by decide) t htfix htmove htsq htnorm htrans
    hthick hodd hexchange hsign
  have hrot : rotationOrder Q = 6 := pathFiniteQuotient_simple_product_order h c 6
    (by decide) t htfix htmove htsq htnorm htrans hthick hodd hexchange hsign
  let j : Iso
      (Chapter6.Source.RankOneGeneric.Global.sourceParabolicAmalgam L (reducedSylow L S))
      (reducedAmalgam L S) :=
    NativeRestoration.subgroupCongrIso _ _ _ _ rfl
      (lemma_F_1_3_6 (reduced_hypothesis h)) rfl
  exact FongSeitzBinary.LinearHexagon.marked_unequal_linear_triality Q (j.trans mark)
    (reduced_hypothesis h) split hrot 0 1 (by decide)
    ((μ false).trans (Theory.PSL2.sl2QuotientEquiv (k false)))
    ((μ true).trans (Theory.PSL2.sl2QuotientEquiv (k true))) ha hab hsmall hlarge

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
