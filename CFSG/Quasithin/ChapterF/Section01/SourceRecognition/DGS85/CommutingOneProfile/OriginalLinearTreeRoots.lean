module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalLinearSource

/-!
# Original linear source roots and apartment quotient orders

The proved original linear path profile supplies five-walk transitivity
and odd five-path fixers on the full-Borel universal tree. Its valences
are the cardinalities of the two original marked fields plus one.
Thus the actual four-path two-cores act sharply transitively on exits,
and each root order is the cardinality of its own original field.

The apartment-exchange application preserves these orders through the
literal quotient map, together with q_alpha=q_beta^2. No earlier-local,
catalogue, escaping-path or path-transitivity premise remains. Compatible
Cartans, reflections and apartment exchange still belong to final marked
recognition; a list of root orders does not identify the amalgam.
Source: DGS, Groups and Graphs (1985), (11.7)(f), pp.174--175,
(14.1)--(14.2), pp.210--211, and universal covers (3.6)--(3.7), pp.77--80.
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
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L₀ i ⧸ pCore 2 (family L₀ i)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K i))
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1) (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
include h K e hc hb hcomm

/-- The actual universal cover has the valences of the two original fields. -/
theorem original_linear_tree_neighbor_cards (x : Subgroup.CosetGeometry.Vertex T) :
    Nat.card ((sourceGraph A).neighborSet x) = Nat.card (K x.type)+1 := by
  obtain ⟨m,hm,hka,hkb,hval⟩ := original_linear_field_and_valences h K e hc hb hcomm
  let cover := NoncommutingProfile.bOne_tree_cover h
  have he := Nat.card_congr
    (Equiv.ofBijective (cover.hom.mapNeighborSet x) (cover.neighbor_bijective x))
  rw [he,hval]
  change 2^(if x.type then m else 2*m)+1 = Nat.card (K x.type)+1
  cases x.type
  · simp only [Bool.false_eq_true,if_false,hka]
  · simp only [if_true,hkb]

/-- The original field sizes supply the third neighbor required by the reflection construction. -/
theorem original_linear_tree_thickness (t : Bool → (A).Universal) :
    ∀ i, ∃ z, (sourceGraph A).Adj (Subgroup.CosetGeometry.base T i) z ∧
      z ≠ Subgroup.CosetGeometry.base T (!i) ∧ z ≠ t i • Subgroup.CosetGeometry.base T (!i) := by
  intro i
  have hcard := original_linear_tree_neighbor_cards h K e hc hb hcomm
    (Subgroup.CosetGeometry.base T i)
  change Nat.card ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)) =
    Nat.card (K i)+1 at hcard
  let : Finite ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.succ_ne_zero _)
  have hlarge : 2 < ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)).ncard := by
    rw [←Nat.card_coe_set_eq,hcard]
    have hh : 1 < Nat.card (K i) := by
      let : Fintype (K i) := Fintype.ofFinite _
      simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card (α := K i))
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

/-- Chapter 14 roots on the original full-Borel tree, constructed without
any Chapter 11 path or local-structure callback. -/
@[expose] def original_linear_pathRoots : Bool → LocalRootAction (X := (A).Universal) (sourceGraph A) :=
  ReducedCartan.pathRoots h cartans 4 (by decide) t htfix htmove htsq htnorm
    (original_linear_tree_path_profile h K e hc hb hcomm).1
    (original_linear_tree_thickness h K e hc hb hcomm t)

local notation "ρ" => original_linear_pathRoots h K e hc hb hcomm cartans t htfix htmove htsq htnorm

/-- The literal source roots act sharply transitively on endpoint exits. -/
theorem original_linear_pathRoots_sharply_transitive (i : Bool) (z : Subgroup.CosetGeometry.Vertex T)
    (hz : (sourceGraph A).Adj (ρ i).a z) (hzprev : z ≠ (ρ i).b) :
    ∃! x : (ρ i).root, (x : (A).Universal) • (ρ i).c = z :=
  ReducedCartan.pathRoots_sharply_transitive h cartans 4 (by decide) t htfix htmove htsq htnorm
    (original_linear_tree_path_profile h K e hc hb hcomm).1
    (original_linear_tree_thickness h K e hc hb hcomm t)
    (original_linear_tree_path_profile h K e hc hb hcomm).2 i z hz hzprev

/-- The root order is the cardinality of its original marked field. -/
theorem original_linear_pathRoots_card (i : Bool) : Nat.card (ρ i).root = Nat.card (K i) := by
  have hh := ReducedCartan.pathRoots_card_add_one h cartans 4 (by decide) t htfix htmove htsq htnorm
    (original_linear_tree_path_profile h K e hc hb hcomm).1
    (original_linear_tree_thickness h K e hc hb hcomm t)
    (original_linear_tree_path_profile h K e hc hb hcomm).2 i
  rw [original_linear_tree_neighbor_cards h K e hc hb hcomm] at hh
  change Nat.card (ρ i).root + 1 = Nat.card (K i)+1 at hh
  omega

/-- The actual apartment quotient preserves each original root order and
the source field relation; compatible Cartans and exchange remain explicit. -/
theorem original_linear_pathRoots_quotient_orders
    (hexchange : ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
      (cartanApartment A (ReducedCartan.apartmentGroup cartans ρ)) 4) :
    Nat.card (K false) = Nat.card (K true)^2 ∧ ∀ i : Bool,
      Nat.card (ρ i).root = Nat.card (K i) ∧
      Nat.card ((ρ i).root.map (quotientMap A
        (cartanApartment A (ReducedCartan.apartmentGroup cartans ρ)) 4)) = Nat.card (K i) := by
  refine ⟨(original_borel_linear_core_profile h K e hc hb hcomm).1,fun i => ⟨?_,?_⟩⟩
  · exact original_linear_pathRoots_card h K e hc hb hcomm cartans t htfix htmove htsq htnorm i
  · exact (ReducedCartan.pathRoots_card_quotientImage h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_linear_tree_path_profile h K e hc hb hcomm).1
      (original_linear_tree_thickness h K e hc hb hcomm t)
      (original_linear_tree_path_profile h K e hc hb hcomm).2 hexchange i).trans
        (original_linear_pathRoots_card h K e hc hb hcomm cartans t htfix htmove htsq htnorm i)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
