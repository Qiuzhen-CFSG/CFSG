module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryPathParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceRootRegularity

/-!
# Elementary four-path roots in the original marked universal tree

The proved elementary five-path profile transfers through the original
full-Borel cover to the actual Chapter 14 tree. The two valences give
thickness and root orders 2^(2m) at alpha and 2^m at beta. Both original
linear quotient markings use this same positive degree.

The actual four-path two-cores act sharply transitively on endpoint exits.
The apartment-exchange consumer preserves their orders through its literal
quotient map. Compatible Cartans, reflections and exchange remain explicit;
the path inputs are discharged. These facts do not identify the amalgam.
Source: DGS85, Groups and Graphs (1985), (11.7)(f), pp.174--175;
(14.1)--(14.2), pp.210--211; universal cover, (3.6)--(3.7), pp.77--80.
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
variable
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems (Reduction.reducedFamily L₀ S₀))
    {c : Vertex (Reduction.reducedFamily L₀ S₀)} (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (hbc : (graph (Reduction.reducedFamily L₀ S₀)).Adj (base (Reduction.reducedFamily L₀ S₀) true) c) (hac : (base (Reduction.reducedFamily L₀ S₀) false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
      pCore 2 ((d.localGroup (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
      pCore 2 ((d.localGroup (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)))
    (g : (Reduction.G₀ L₀ S₀)) (hga : g ∈ stabilizer (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false))
    (hgb : g • (base (Reduction.reducedFamily L₀ S₀) true) ≠ (base (Reduction.reducedFamily L₀ S₀) true))
    (hesc : ¬ (Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ≤
      (Q (Reduction.reducedFamily L₀ S₀) (g • (base (Reduction.reducedFamily L₀ S₀) true))).map ((Reduction.G₀ L₀ S₀)).subtype)
    {v : Vertex (Reduction.reducedFamily L₀ S₀)} {r : ℕ}
    (ht : RootPathTransitive (graph (Reduction.reducedFamily L₀ S₀)) (Reduction.G₀ L₀ S₀) v (r+1))
    (p : BasedWalk (graph (Reduction.reducedFamily L₀ S₀)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base (Reduction.reducedFamily L₀ S₀) false) ∈ p.vertices) (hbp : (base (Reduction.reducedFamily L₀ S₀) true) ∈ p.vertices)
    (hcp : c ∈ p.vertices) (hgbp : g • (base (Reduction.reducedFamily L₀ S₀) true) ∈ p.vertices)
    (hgcp : g • c ∈ p.vertices)
    (helem : ∃ hN : (((Q (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype).subgroupOf
          (twoCore (commonBorel L₀ S₀))))

include h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem

/-- Both Chapter 14 path inputs on the actual universal tree, using the
original endpoint inclusions and the whole reduced Borel. -/
theorem elementary_tree_path_profile_on_escaping_path :
    BasedPathTransitive (X := (A).Universal) (sourceGraph A) 5 ∧
      ∀ {x y} (q : (sourceGraph A).Walk x y), q.IsPath → q.length = 5 →
        Odd (Nat.card (pathFixer (X := (A).Universal) q)) :=
  original_borel_elementary_cover_path_profile_on_escaping_path h d hc hb hcomm hbc hac Ma Mb
    g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem T
    (NoncommutingProfile.bOne_tree_map h) (NoncommutingProfile.bOne_tree_cover h)

/-- The universal tree has the original elementary valences in their original
orientation; no quotient or field degree is replaced. -/
theorem elementary_tree_neighbor_cards_on_escaping_path :
    ∃ m : ℕ, 0 < m ∧
      (ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
       ClassicalGroup.IsPSL ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 2 (2^m)) ∧ ∀ x : Subgroup.CosetGeometry.Vertex T,
      Nat.card ((sourceGraph A).neighborSet x) = 2^(if x.type then m else 2*m)+1 := by
  obtain ⟨m,hm,mark,hval,_⟩ := original_borel_elementary_walk_geometry_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem
  refine ⟨m,hm,mark,?_⟩
  intro x
  let cover := NoncommutingProfile.bOne_tree_cover h
  have he := Nat.card_congr
    (Equiv.ofBijective (cover.hom.mapNeighborSet x) (cover.neighbor_bijective x))
  exact he.trans (hval (cover.vertex x))

/-- The positive field degree supplies a third neighbor at either original
endpoint, discharging reflection-path thickness. -/
theorem elementary_tree_thickness_on_escaping_path (t : Bool → (A).Universal) :
    ∀ i, ∃ z, (sourceGraph A).Adj (Subgroup.CosetGeometry.base T i) z ∧
      z ≠ Subgroup.CosetGeometry.base T (!i) ∧ z ≠ t i • Subgroup.CosetGeometry.base T (!i) := by
  obtain ⟨m,hm,_,hval⟩ := elementary_tree_neighbor_cards_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem
  intro i
  have hcard := hval (Subgroup.CosetGeometry.base T i)
  change Nat.card ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)) =
    2^(if i then m else 2*m)+1 at hcard
  let : Finite ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.succ_ne_zero _)
  have hlarge : 2 < ((sourceGraph A).neighborSet (Subgroup.CosetGeometry.base T i)).ncard := by
    rw [←Nat.card_coe_set_eq,hcard]
    have he : (if i then m else 2*m) ≠ 0 := by cases i <;> simp <;> omega
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

/-- The actual four-path roots with the source path inputs discharged. -/
@[expose] def elementary_pathRoots : Bool → LocalRootAction (X := (A).Universal) (sourceGraph A) :=
  ReducedCartan.pathRoots h cartans 4 (by decide) t htfix htmove htsq htnorm
    (elementary_tree_path_profile_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem).1
    (elementary_tree_thickness_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem t)

local notation "ρ" => elementary_pathRoots h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
  ht p hp ha hbp hcp hgbp hgcp helem cartans t htfix htmove htsq htnorm

/-- Literal application to Chapter 14: both original roots act sharply
transitively on their exits. Compatible Cartans and reflections remain explicit. -/
theorem elementary_pathRoots_sharply_transitive (i : Bool) (z : Subgroup.CosetGeometry.Vertex T)
    (hz : (sourceGraph A).Adj (ρ i).a z) (hzprev : z ≠ (ρ i).b) :
    ∃! x : (ρ i).root, (x : (A).Universal) • (ρ i).c = z :=
  ReducedCartan.pathRoots_sharply_transitive h cartans 4 (by decide) t htfix htmove htsq htnorm
    (elementary_tree_path_profile_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem).1
    (elementary_tree_thickness_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem t)
    (elementary_tree_path_profile_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem).2 i z hz hzprev

/-- Both root orders use the same positive field degree in the original
orientation: q_beta squared at alpha and q_beta at beta. -/
theorem elementary_pathRoots_orders :
    ∃ m : ℕ, 0 < m ∧
      (ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
       ClassicalGroup.IsPSL ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 2 (2^m)) ∧ ∀ i : Bool, Nat.card (ρ i).root = 2^(if i then m else 2*m) := by
  obtain ⟨m,hm,mark,hval⟩ := elementary_tree_neighbor_cards_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem
  refine ⟨m,hm,mark,?_⟩
  intro i
  have hh := ReducedCartan.pathRoots_card_add_one h cartans 4 (by decide) t htfix htmove htsq htnorm
    (elementary_tree_path_profile_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem).1
    (elementary_tree_thickness_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem t)
    (elementary_tree_path_profile_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem).2 i
  rw [hval] at hh
  change Nat.card (ρ i).root + 1 = 2^(if i then m else 2*m)+1 at hh
  omega

/-- The literal apartment quotient preserves both original root orders.
Exchange remains with its source owner; the path premises are discharged. -/
theorem elementary_pathRoots_quotient_orders
    (hexchange : ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
      (cartanApartment A (ReducedCartan.apartmentGroup cartans ρ)) 4) :
    ∃ m : ℕ, 0 < m ∧
      (ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
       ClassicalGroup.IsPSL ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 2 (2^m)) ∧ ∀ i : Bool,
      Nat.card (ρ i).root = 2^(if i then m else 2*m) ∧
      Nat.card ((ρ i).root.map (quotientMap A
        (cartanApartment A (ReducedCartan.apartmentGroup cartans ρ)) 4)) = 2^(if i then m else 2*m) := by
  obtain ⟨m,hm,mark,hord⟩ := elementary_pathRoots_orders h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
    ht p hp ha hbp hcp hgbp hgcp helem cartans t htfix htmove htsq htnorm
  refine ⟨m,hm,mark,fun i => ⟨hord i,?_⟩⟩
  exact (ReducedCartan.pathRoots_card_quotientImage h cartans 4 (by decide) t htfix htmove htsq htnorm
    (elementary_tree_path_profile_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem).1
    (elementary_tree_thickness_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem t)
    (elementary_tree_path_profile_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc
      ht p hp ha hbp hcp hgbp hgcp helem).2 hexchange i).trans (hord i)

/-! The thickness input also gives the involution needed before the Chapter 14
conjugacy choice.  This keeps the full local permutation kernel in the
conclusion; it is not identified with its 2-core. -/
theorem elementary_pathRoots_involution_outside_localKernel (i : Bool) :
    ∃ x ∈ (ρ i).root, orderOf x = 2 ∧
      x ∉ ballKernel (Universal.cosetFamily A)
        (Subgroup.CosetGeometry.base (Universal.cosetFamily A) i) 1 := by
  exact ReducedCartan.pathRoots_exists_involution_outside_localKernel h cartans 4
    (by decide) t htfix htmove htsq htnorm
    (elementary_tree_path_profile_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g
      hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem).1
    (elementary_tree_thickness_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g
      hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem t)
    (elementary_tree_path_profile_on_escaping_path h d hc hb hcomm hbc hac Ma Mb g
      hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem).2 i

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
