module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedPathRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceRootRegularity

/-!
# Mixed source paths in the marked universal tree

The full-Borel covering transports the proved mixed five-path transitivity
and odd five-path fixers to the universal tree of the original reduced
amalgam. Its original endpoint valences are five and three, which also
supply the thickness needed for the chosen reflection paths.

Applying the apartment construction to these inputs gives actual four-path
two-cores acting sharply transitively on the exits, of orders four and two
in the original endpoint order. Under apartment exchange, their images in
the literal quotient retain those orders. Compatible Cartans, reflection
choices and exchange remain explicit inputs for their source assembly
owners; all path-profile and thickness premises are discharged here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.7)(f), pp.174--175; (14.1)--(14.2), pp.210--211; (3.6)--(3.7), pp.77--80.
-/

public noncomputable section
open Subgroup SimpleGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] [Finite G] (K U₀ S : Subgroup G)
local notation "F" => reducedFamily ![K,U₀] S
local notation "α" => base F false
local notation "β" => base F true
local notation "A" => reducedAmalgam ![K,U₀] S
local notation "T" => Universal.cosetFamily A

/-- The two exact path hypotheses for Chapter 14 hold on its original
universal tree, through the full-Borel covering and original endpoint maps. -/
theorem mixed_tree_path_profile (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    BasedPathTransitive (X := (A).Universal) (sourceGraph A) 5 ∧
      ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length = 5 →
        Odd (Nat.card (pathFixer (X := (A).Universal) p)) :=
  mixed_cover_path_profile K U₀ S h eK eU hc hb hcomm T
    (NoncommutingProfile.bOne_tree_map h) (NoncommutingProfile.bOne_tree_cover h)

/-- The universal cover preserves both original local valences. -/
theorem mixed_tree_neighbor_cards (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3)) (v : Subgroup.CosetGeometry.Vertex T) :
    Nat.card ((sourceGraph A).neighborSet v) = if v.type then 3 else 5 := by
  let c := NoncommutingProfile.bOne_tree_cover h
  have he := Nat.card_congr (Equiv.ofBijective (c.hom.mapNeighborSet v) (c.neighbor_bijective v))
  exact he.trans (mixed_reduced_neighbor_cards K U₀ S h eK eU (c.vertex v))

/-- Three or five neighbors supply an exit distinct from either prescribed
neighbor, discharging the thickness premise for the reflection paths. -/
theorem mixed_tree_thickness (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (t : Bool → (A).Universal) :
    ∀ i, ∃ z, (sourceGraph A).Adj (Subgroup.CosetGeometry.base T i) z ∧
      z ≠ Subgroup.CosetGeometry.base T (!i) ∧ z ≠ t i • Subgroup.CosetGeometry.base T (!i) := by
  intro i
  have hc := mixed_tree_neighbor_cards K U₀ S h eK eU (Subgroup.CosetGeometry.base T i)
  let : Finite ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; change (if i then 3 else 5) ≠ 0; cases i <;> decide)
  have hcard : 2 < ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)).ncard := by
    rw [←Nat.card_coe_set_eq,hc]; change 2 < (if i then 3 else 5); cases i <;> decide
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp hcard
  by_cases hx' : x ≠ Subgroup.CosetGeometry.base T (!i) ∧ x ≠ t i • Subgroup.CosetGeometry.base T (!i)
  · exact ⟨x,hx,hx'⟩
  by_cases hy' : y ≠ Subgroup.CosetGeometry.base T (!i) ∧ y ≠ t i • Subgroup.CosetGeometry.base T (!i)
  · exact ⟨y,hy,hy'⟩
  exact ⟨z,hz,by aesop⟩

variable (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair (reducedFamily ![K,U₀] S)
      (base (reducedFamily ![K,U₀] S) false) (base (reducedFamily ![K,U₀] S) true))
    (hb : DGS85.b (reducedFamily ![K,U₀] S) = 1)
    (hcomm : ⁅Z (reducedFamily ![K,U₀] S) (base (reducedFamily ![K,U₀] S) false),
      Z (reducedFamily ![K,U₀] S) (base (reducedFamily ![K,U₀] S) true)⁆ = ⊥)
    (c : CompatibleCartans ![K,U₀] (reducedSylow ![K,U₀] S))
    (t : Bool → (reducedAmalgam ![K,U₀] S).Universal)
    (htfix : ∀ i,
      t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam ![K,U₀] S)) i =
        Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam ![K,U₀] S)) i)
    (htmove : ∀ i,
      t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam ![K,U₀] S)) (!i) ≠
        Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam ![K,U₀] S)) (!i))
    (htsq : ∀ i, t i * t i = 1)
    (htnorm : ∀ i,
      t i ∈ normalizer (ReducedCartan.cartan c : Set (reducedAmalgam ![K,U₀] S).Universal))

/-- Both four-path roots constructed from the actual mixed path profile. -/
@[expose] def mixed_pathRoots : Bool → LocalRootAction (X := (A).Universal) (sourceGraph A) :=
  ReducedCartan.pathRoots (L := ![K,U₀]) (S := S) h c 4 (by decide) t htfix htmove htsq htnorm
    (mixed_tree_path_profile K U₀ S h eK eU hc hb hcomm).1
    (mixed_tree_thickness K U₀ S h eK eU t)

local notation "ρ" => mixed_pathRoots K U₀ S h eK eU hc hb hcomm c t htfix htmove htsq htnorm

/-- Literal application of the mixed Chapter 11 profile to the chosen Chapter 14
roots. Reflection and compatible-Cartan data remain with their source owners;
path transitivity, odd five-path fixers and thickness are discharged here. -/
theorem mixed_pathRoots_sharply_transitive (i : Bool) (z : Subgroup.CosetGeometry.Vertex T)
    (hz : (sourceGraph A).Adj (ρ i).a z) (hzprev : z ≠ (ρ i).b) :
    ∃! x : (ρ i).root, (x : (A).Universal) • (ρ i).c = z :=
  ReducedCartan.pathRoots_sharply_transitive (L := ![K,U₀]) (S := S)
    h c 4 (by decide) t htfix htmove htsq htnorm
    (mixed_tree_path_profile K U₀ S h eK eU hc hb hcomm).1
    (mixed_tree_thickness K U₀ S h eK eU t)
    (mixed_tree_path_profile K U₀ S h eK eU hc hb hcomm).2 i z hz hzprev

/-- The actual four-path radicals have their original oriented orders:
four at the A₅ endpoint and two at the cubic endpoint. -/
theorem mixed_pathRoots_card (i : Bool) : Nat.card (ρ i).root = if i then 2 else 4 := by
  have hh := ReducedCartan.pathRoots_card_add_one (L := ![K,U₀]) (S := S)
    h c 4 (by decide) t htfix htmove htsq htnorm
    (mixed_tree_path_profile K U₀ S h eK eU hc hb hcomm).1
    (mixed_tree_thickness K U₀ S h eK eU t)
    (mixed_tree_path_profile K U₀ S h eK eU hc hb hcomm).2 i
  rw [mixed_tree_neighbor_cards K U₀ S h eK eU] at hh
  change Nat.card (ρ i).root + 1 = (if i then 3 else 5) at hh
  cases i <;> simp only [Bool.false_eq_true,ite_false,ite_true] at * <;> omega

/-- On the literal apartment quotient, exchange preserves the two original
oriented root orders. The path hypotheses in this quotient-order consumer
are discharged by the mixed source profile. -/
theorem mixed_pathRoots_card_quotientImage
    (hexchange : ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
      (cartanApartment A (ReducedCartan.apartmentGroup c ρ)) 4) (i : Bool) :
    Nat.card ((ρ i).root.map (quotientMap A
      (cartanApartment A (ReducedCartan.apartmentGroup c ρ)) 4)) = if i then 2 else 4 :=
  (ReducedCartan.pathRoots_card_quotientImage (L := ![K,U₀]) (S := S)
    h c 4 (by decide) t htfix htmove htsq htnorm
    (mixed_tree_path_profile K U₀ S h eK eU hc hb hcomm).1
    (mixed_tree_thickness K U₀ S h eK eU t)
    (mixed_tree_path_profile K U₀ S h eK eU hc hb hcomm).2 hexchange i).trans
      (mixed_pathRoots_card K U₀ S h eK eU hc hb hcomm c t htfix htmove htsq htnorm i)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
