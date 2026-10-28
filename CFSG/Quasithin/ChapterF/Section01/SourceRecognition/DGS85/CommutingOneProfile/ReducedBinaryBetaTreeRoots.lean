module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBinaryBetaPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceRootRegularity

/-!
# Intrinsically marked binary source paths in the universal tree

The actual reduced PSL2(4)/SL2(2) markings give five-path transitivity,
odd five-path fixers and degrees five and three. The full-Borel covering
carries them to the universal tree of the original reduced amalgam.
Its four-path two-cores therefore act sharply transitively on exits and
have orders four and two in the original endpoint order.

The literal apartment quotient preserves these root orders under exchange.
Compatible Cartans, reflection choices and exchange remain earlier-source
inputs; no local quotient list is treated as a marked amalgam isomorphism.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.7)(f), pp.174--175, (14.1)--(14.2), pp.210--211.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open CommutingNontrivial
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] [Finite G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A

/-- The two exact path hypotheses for Chapter 14 hold on its original
universal tree, through the full-Borel covering and original endpoint maps. -/
theorem reduced_four_binary_tree_path_profile (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems (reducedFamily L S))
    (ha : ClassicalGroup.IsPSL
      (d.localGroup (base (reducedFamily L S) false) ⧸
        pCore 2 (d.localGroup (base (reducedFamily L S) false))) 2 4)
    (eb : (d.localGroup (base (reducedFamily L S) true) ⧸
      pCore 2 (d.localGroup (base (reducedFamily L S) true))) ≃* SL(2,ZMod 2))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    BasedPathTransitive (X := (A).Universal) (sourceGraph A) 5 ∧
      ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length = 5 →
        Odd (Nat.card (pathFixer (X := (A).Universal) p)) :=
  reduced_four_binary_cover_path_profile h d hc hb hcomm ha eb T
    (NoncommutingProfile.bOne_tree_map h) (NoncommutingProfile.bOne_tree_cover h)

omit [Finite G] in
/-- The universal cover preserves both original local valences. -/
theorem reduced_four_binary_tree_neighbor_cards (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems (reducedFamily L S))
    (ha : ClassicalGroup.IsPSL
      (d.localGroup (base (reducedFamily L S) false) ⧸
        pCore 2 (d.localGroup (base (reducedFamily L S) false))) 2 4)
    (eb : (d.localGroup (base (reducedFamily L S) true) ⧸
      pCore 2 (d.localGroup (base (reducedFamily L S) true))) ≃* SL(2,ZMod 2)) (v : Subgroup.CosetGeometry.Vertex T) :
    Nat.card ((sourceGraph A).neighborSet v) = if v.type then 3 else 5 := by
  let c := NoncommutingProfile.bOne_tree_cover h
  have he := Nat.card_congr (Equiv.ofBijective (c.hom.mapNeighborSet v) (c.neighbor_bijective v))
  exact he.trans (reduced_four_binary_neighbor_cards h d ha eb (c.vertex v))

omit [Finite G] in
/-- Three or five neighbors supply an exit distinct from either prescribed
neighbor, discharging the thickness premise for the reflection paths. -/
theorem reduced_four_binary_tree_thickness (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems (reducedFamily L S))
    (ha : ClassicalGroup.IsPSL
      (d.localGroup (base (reducedFamily L S) false) ⧸
        pCore 2 (d.localGroup (base (reducedFamily L S) false))) 2 4)
    (eb : (d.localGroup (base (reducedFamily L S) true) ⧸
      pCore 2 (d.localGroup (base (reducedFamily L S) true))) ≃* SL(2,ZMod 2))
    (t : Bool → (A).Universal) :
    ∀ i, ∃ z, (sourceGraph A).Adj (Subgroup.CosetGeometry.base T i) z ∧
      z ≠ Subgroup.CosetGeometry.base T (!i) ∧ z ≠ t i • Subgroup.CosetGeometry.base T (!i) := by
  intro i
  have hc := reduced_four_binary_tree_neighbor_cards h d ha eb (Subgroup.CosetGeometry.base T i)
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

variable (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems (reducedFamily L S))
    (ha : ClassicalGroup.IsPSL
      (d.localGroup (base (reducedFamily L S) false) ⧸
        pCore 2 (d.localGroup (base (reducedFamily L S) false))) 2 4)
    (eb : (d.localGroup (base (reducedFamily L S) true) ⧸
      pCore 2 (d.localGroup (base (reducedFamily L S) true))) ≃* SL(2,ZMod 2))
    (hc : IsCriticalPair (reducedFamily L S)
      (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i,
      t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L S)) i =
        Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i,
      t i • Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
        Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i * t i = 1)
    (htnorm : ∀ i,
      t i ∈ normalizer (ReducedCartan.cartan c : Set (reducedAmalgam L S).Universal))

/-- Both four-path roots constructed from the actual mixed path profile. -/
@[expose] def reduced_four_binary_pathRoots : Bool → LocalRootAction (X := (A).Universal) (sourceGraph A) :=
  ReducedCartan.pathRoots (L := L) (S := S) h c 4 (by decide) t htfix htmove htsq htnorm
    (reduced_four_binary_tree_path_profile h d ha eb hc hb hcomm).1
    (reduced_four_binary_tree_thickness h d ha eb t)

local notation "ρ" => reduced_four_binary_pathRoots h d ha eb hc hb hcomm c t htfix htmove htsq htnorm

/-- Literal application of the mixed Chapter 11 profile to the chosen Chapter 14
roots. Reflection and compatible-Cartan data remain with their source owners;
path transitivity, odd five-path fixers and thickness are discharged here. -/
theorem reduced_four_binary_pathRoots_sharply_transitive (i : Bool) (z : Subgroup.CosetGeometry.Vertex T)
    (hz : (sourceGraph A).Adj (ρ i).a z) (hzprev : z ≠ (ρ i).b) :
    ∃! x : (ρ i).root, (x : (A).Universal) • (ρ i).c = z :=
  ReducedCartan.pathRoots_sharply_transitive (L := L) (S := S)
    h c 4 (by decide) t htfix htmove htsq htnorm
    (reduced_four_binary_tree_path_profile h d ha eb hc hb hcomm).1
    (reduced_four_binary_tree_thickness h d ha eb t)
    (reduced_four_binary_tree_path_profile h d ha eb hc hb hcomm).2 i z hz hzprev

/-- The actual four-path radicals have their original oriented orders:
four at the A₅ endpoint and two at the cubic endpoint. -/
theorem reduced_four_binary_pathRoots_card (i : Bool) : Nat.card (ρ i).root = if i then 2 else 4 := by
  have hh := ReducedCartan.pathRoots_card_add_one (L := L) (S := S)
    h c 4 (by decide) t htfix htmove htsq htnorm
    (reduced_four_binary_tree_path_profile h d ha eb hc hb hcomm).1
    (reduced_four_binary_tree_thickness h d ha eb t)
    (reduced_four_binary_tree_path_profile h d ha eb hc hb hcomm).2 i
  rw [reduced_four_binary_tree_neighbor_cards h d ha eb] at hh
  change Nat.card (ρ i).root + 1 = (if i then 3 else 5) at hh
  cases i <;> simp only [Bool.false_eq_true,ite_false,ite_true] at * <;> omega

/-- On the literal apartment quotient, exchange preserves the two original
oriented root orders. The path hypotheses in this quotient-order consumer
are discharged by the mixed source profile. -/
theorem reduced_four_binary_pathRoots_card_quotientImage
    (hexchange : ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
      (cartanApartment A (ReducedCartan.apartmentGroup c ρ)) 4) (i : Bool) :
    Nat.card ((ρ i).root.map (quotientMap A
      (cartanApartment A (ReducedCartan.apartmentGroup c ρ)) 4)) = if i then 2 else 4 :=
  (ReducedCartan.pathRoots_card_quotientImage (L := L) (S := S)
    h c 4 (by decide) t htfix htmove htsq htnorm
    (reduced_four_binary_tree_path_profile h d ha eb hc hb hcomm).1
    (reduced_four_binary_tree_thickness h d ha eb t)
    (reduced_four_binary_tree_path_profile h d ha eb hc hb hcomm).2 hexchange i).trans
      (reduced_four_binary_pathRoots_card h d ha eb hc hb hcomm c t htfix htmove htsq htnorm i)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
