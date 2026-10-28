module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryComplete

/-!
# Original marked unitary roots and apartment quotient

The original PSU3 or SU3 marking supplies the five-walk profile on the
full-Borel universal tree. The same marked degree determines both tree
valences, hence the thickness needed to construct the four-path roots.
The literal two-cores of those path fixers act sharply transitively on exits.
Their orders are 2^(2m) at alpha and 2^(3m) at beta, and the actual apartment
quotient preserves both orders.

All Chapter 11 path and thickness premises are discharged. The source alpha
catalogue, both original unitary covers and every positive degree are retained.
Compatible Cartans, the specified reflections and apartment exchange remain
inputs of marked recognition; their producers and final assembly are distinct.
The graph is used through its actual universal cover and need not itself be a tree.
Source: DGS85, Groups and Graphs (1985), (11.8)(g), pp.176--177;
(14.1)--(14.2), pp.210--211; universal covers (3.6)--(3.7), pp.77--80.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀
local notation "A" => reducedAmalgam L₀ S₀
local notation "T" => Universal.cosetFamily A
variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)) 3 (2^m) ∨
      IsSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)) 3 (2^m))

include h hc hb hcomm Ma hm mark

/-- The universal cover retains the valences of the original marked degree. -/
theorem original_unitary_tree_neighbor_cards_from_marking
    (x : Subgroup.CosetGeometry.Vertex T) :
    Nat.card ((sourceGraph A).neighborSet x) = 2^(if x.type then 3*m else 2*m)+1 := by
  let cover := NoncommutingProfile.bOne_tree_cover h
  have he := Nat.card_congr
    (Equiv.ofBijective (cover.hom.mapNeighborSet x) (cover.neighbor_bijective x))
  exact he.trans ((original_unitary_field_and_valences h hc hb hcomm Ma hm mark).2 (cover.vertex x))

/-- The supplied positive degree gives the third neighbor needed at each root. -/
theorem original_unitary_tree_thickness_from_marking (t : Bool → (A).Universal) :
    ∀ i, ∃ z, (sourceGraph A).Adj (Subgroup.CosetGeometry.base T i) z ∧
      z ≠ Subgroup.CosetGeometry.base T (!i) ∧ z ≠ t i • Subgroup.CosetGeometry.base T (!i) := by
  intro i
  have hcard := original_unitary_tree_neighbor_cards_from_marking h hc hb hcomm Ma hm mark
    (Subgroup.CosetGeometry.base T i)
  change Nat.card ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)) =
    2^(if i then 3*m else 2*m)+1 at hcard
  let : Finite ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.succ_ne_zero _)
  have hlarge : 2 < ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)).ncard := by
    rw [←Nat.card_coe_set_eq,hcard]
    have he : (if i then 3*m else 2*m) ≠ 0 := by cases i <;> simp <;> omega
    have := one_lt_pow₀ (by decide : 1 < (2:ℕ)) he
    omega
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp hlarge
  by_cases hx' : x ≠ Subgroup.CosetGeometry.base T (!i) ∧ x ≠ t i • Subgroup.CosetGeometry.base T (!i)
  · exact ⟨x,hx,hx'⟩
  by_cases hy' : y ≠ Subgroup.CosetGeometry.base T (!i) ∧ y ≠ t i • Subgroup.CosetGeometry.base T (!i)
  · exact ⟨y,hy,hy'⟩
  exact ⟨z,hz,by aesop⟩

variable (cartans : CompatibleCartans L₀ (reducedSylow L₀ S₀))
    (t : Bool → (reducedAmalgam L₀ S₀).Universal)
    (htfix : ∀ i, t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i = Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i)
    (htmove : ∀ i, t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i) ≠ Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i))
    (htsq : ∀ i, t i*t i = 1)
    (htnorm : ∀ i, t i ∈ normalizer (ReducedCartan.cartan cartans : Set (reducedAmalgam L₀ S₀).Universal))

/-- Chapter 14 roots on the original full-Borel tree, with
Chapter 11 path and thickness premises discharged. -/
@[expose] def original_unitary_pathRoots_from_marking : Bool → LocalRootAction (X := (A).Universal) (sourceGraph A) :=
  ReducedCartan.pathRoots h cartans 4 (by decide) t htfix htmove htsq htnorm
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
    (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t)

local notation "ρ" => original_unitary_pathRoots_from_marking h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm

/-- The literal source roots act sharply transitively on endpoint exits. -/
theorem original_unitary_pathRoots_from_marking_sharply_transitive (i : Bool) (z : Subgroup.CosetGeometry.Vertex T)
    (hz : (sourceGraph A).Adj (ρ i).a z) (hzprev : z ≠ (ρ i).b) :
    ∃! x : (ρ i).root, (x : (A).Universal) • (ρ i).c = z :=
  ReducedCartan.pathRoots_sharply_transitive h cartans 4 (by decide) t htfix htmove htsq htnorm
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
    (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t)
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).2 i z hz hzprev

/-- The alpha and beta root orders use the square and cube of the same marked field. -/
theorem original_unitary_pathRoots_from_marking_card (i : Bool) : Nat.card (ρ i).root = 2^(if i then 3*m else 2*m) := by
  have hh := ReducedCartan.pathRoots_card_add_one h cartans 4 (by decide) t htfix htmove htsq htnorm
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
    (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t)
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).2 i
  rw [original_unitary_tree_neighbor_cards_from_marking h hc hb hcomm Ma hm mark] at hh
  change Nat.card (ρ i).root + 1 = 2^(if i then 3*m else 2*m)+1 at hh
  omega

/-- The literal apartment quotient preserves both root orders at the same
original marked degree. Cartans, reflections and exchange remain explicit. -/
theorem original_unitary_pathRoots_from_marking_quotient_orders
    (hexchange : ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
      (cartanApartment A (ReducedCartan.apartmentGroup cartans ρ)) 4) :
    ∀ i : Bool, Nat.card (ρ i).root = 2^(if i then 3*m else 2*m) ∧
      Nat.card ((ρ i).root.map (quotientMap A
        (cartanApartment A (ReducedCartan.apartmentGroup cartans ρ)) 4)) =
          2^(if i then 3*m else 2*m) := by
  intro i
  refine ⟨original_unitary_pathRoots_from_marking_card h hc hb hcomm Ma hm mark
    cartans t htfix htmove htsq htnorm i,?_⟩
  exact (ReducedCartan.pathRoots_card_quotientImage h cartans 4 (by decide) t htfix htmove htsq htnorm
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
    (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t)
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).2 hexchange i).trans
      (original_unitary_pathRoots_from_marking_card h hc hb hcomm Ma hm mark
        cartans t htfix htmove htsq htnorm i)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
