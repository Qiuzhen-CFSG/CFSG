module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedLinearPathFixers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryPathProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.TwoPowerPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OddValenceSourcePaths

/-!
# The elementary source path parameters r=4 and s=5

The literal elementary quotient of the full original Borel selects both
linear endpoint markings. Their degrees satisfy n=2m. The actual valences
are 2^(2m)+1 and 2^m+1, while each edge two-core has order 2^(6m).
This equals the number of five-walks extending that edge. Odd five-walk
fixers make its action free, hence transitive. Shorter walks are regular;
odd longer fixers cannot act transitively on an even exit set.

The source extrema include its closed-path convention. Both original
linear quotient markings, the full Borel and the literal original fixer
images are retained. The cover application supplies the Chapter 14 path
inputs, applied to the actual roots in ElementaryTreeRoots. Earlier local
theorems and the escaping source path remain explicit obligations.
Source: DGS85, Groups and Graphs (1985), (11.7)(f), pp.174--175;
path conventions pp.60,73--74 and the application (14.1), p.210.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Theory.GroupTheory.WeakBNPair.RegularTree Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀
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

/-- The actual valences, five-walk transitivity and odd long-walk fixers
are constructed from the original elementary full-Borel branch. -/
theorem original_borel_elementary_walk_geometry_on_escaping_path :
    ∃ m : ℕ, 0 < m ∧
      (ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
       ClassicalGroup.IsPSL ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 2 (2^m)) ∧
      (∀ x : Vertex F₀, Nat.card ((graph F₀).neighborSet x) =
        2^(if x.type then m else 2*m)+1) ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      (∀ {n : ℕ} {x : Vertex F₀} (q : BasedWalk (graph F₀) n x),
        q.Nonbacktracking → 5 ≤ n → Odd (Nat.card (pathStabilizer F₀ q))) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), 5 ≤ q.length →
        (∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) →
          Odd (Nat.card (pathFixer (X := G₀) q)) := by
  obtain ⟨n,m,hn,hm,markα,markβ,hnm,hS⟩ := original_borel_elementary_profile_on_path
    h d hc hb hcomm hbc hac Ma Mb helem ht p hp ha hbp hcp
  rw [hnm] at markα hS
  have hpoly : (2^(2*m))^2 * (2^m)^2 = (2:ℕ)^(6*m) := by
    rw [←pow_mul,←pow_mul,←pow_add]
    congr 1
    omega
  rw [hpoly] at hS
  have hval := original_reduced_linear_neighbor_cards h d (by omega : 0 < 2*m) hm markα markβ
  have hodd {x y : Vertex F₀} (q : (graph F₀).Walk x y) (hlen : 5 ≤ q.length)
      (hnb : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) :
      Odd (Nat.card (pathFixer (X := G₀) q)) := by
    have hh := original_reduced_linear_long_walk_fixer_odd_on_escaping_path
      h d hc hb hcomm hbc hac (by omega : 0 < 2*m) hm markα markβ
      g hga hgb hesc ht p hp ha hbp hgbp hgcp q hlen hnb
    rwa [card_map_of_injective (G₀).subtype_injective] at hh
  have hbased {n : ℕ} {x : Vertex F₀} (q : BasedWalk (graph F₀) n x)
      (hq : q.Nonbacktracking) (hn : 5 ≤ n) : Odd (Nat.card (pathStabilizer F₀ q)) :=
    based_fixer_odd_of_walk F₀ hodd q hq hn
  let R := (stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2
  have htr := Reduction.reduced_triple h
  have hBG : Reduction.B₀ L₀ S₀ ≤ G₀ :=
    (show Reduction.B₀ L₀ S₀ ≤ Reduction.P₀ L₀ S₀ 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L₀ S₀) ≤ G₀ :=
    (show twoCore (commonBorel L₀ S₀) ≤ Reduction.B₀ L₀ S₀ from le_sup_right).trans hBG
  have hmap : R.map (G₀).subtype = twoCore (commonBorel L₀ S₀) := by
    dsimp only [R]
    rw [show stabilizer F₀ (base F₀ false) = F₀ false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F₀ (base F₀ true) = F₀ true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F₀ false ⊓ F₀ true = (Reduction.B₀ L₀ S₀).subgroupOf G₀ from htr.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,Reduction.B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  rw [←hmap,card_map_of_injective (G₀).subtype_injective] at hS
  have hbase : Nat.card ((F₀ false ⊓ F₀ true).pCoreIn 2) = 2^(6*m) := by
    simpa only [R,Subgroup.CosetGeometry.stabilizer_base] using hS
  have hcard {x y : Vertex F₀} (hxy : (graph F₀).Adj x y) :
      Nat.card ((stabilizer F₀ x ⊓ stabilizer F₀ y).pCoreIn 2) = 2^(6*m) := by
    obtain ⟨t,ht⟩ := edgeStabilizer_map_base F₀ hxy
    rw [ht,Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj t).injective,card_map_of_injective (MulAut.conj t).injective,hbase]
  refine ⟨m,hm,⟨markα,markβ⟩,hval,?_,hbased,hodd⟩
  apply two_power_graph_five_walk_transitive_of_edge_cores F₀ (fun i => if i then m else 2*m) hval
  · intro x y hxy
    simpa only [Bool.false_eq_true,if_false,if_true,show 2*(2*m+m) = 6*m by omega] using hcard hxy
  · intro x q hq
    exact hbased q hq le_rfl

/-- Five-walk transitivity in both source vertex orbits, with the full
original Borel and all field degrees. Its counting and fixer inputs are proved. -/
theorem original_borel_elementary_five_walk_transitive_on_escaping_path (x : Vertex F₀) :
    RootPathTransitive (graph F₀) G₀ x 5 := by
  obtain ⟨_,_,_,_,hfive,_⟩ := original_borel_elementary_walk_geometry_on_escaping_path h d hc hb hcomm hbc hac Ma Mb
    g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem
  exact hfive x

/-- Source (11.7)(f), including the closed-path convention and the literal
fixer images in the original completion. Earlier-source inputs remain explicit. -/
theorem original_borel_elementary_source_path_parameters_on_escaping_path :
    HasSourcePathParameters (P := fun i => (Reduction.P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  obtain ⟨m,hm,_,hval,hfive,hbased,hodd⟩ := original_borel_elementary_walk_geometry_on_escaping_path h d hc hb hcomm hbc hac Ma Mb
    g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem
  have hpos : ∀ i : Bool, 0 < (if i then m else 2*m) := by intro i; cases i <;> simp <;> omega
  have hregular {n : ℕ} {x : Vertex F₀} (q : BasedWalk (graph F₀) n x)
      (hq : q.Nonbacktracking) : Regular (A := G₀) q ↔ n ≤ 4 :=
    two_power_graph_regular_iff_of_five_transitive F₀
      (fun i => if i then m else 2*m) hpos hval hfive (fun q hq hn => hbased q hq hn) q hq
  have hval' (x : Vertex F₀) : 3 ≤ Nat.card ((graph F₀).neighborSet x) ∧
      Odd (Nat.card ((graph F₀).neighborSet x)) := by
    rw [hval]
    have hgt : 1 < 2^(if x.type then m else 2*m) := one_lt_pow₀ (by decide) (by
      have := hpos x.type; omega)
    refine ⟨by omega,?_⟩
    exact Even.add_odd ((by decide : Even (2:ℕ)).pow_of_ne_zero (by
      have := hpos x.type; omega)) (by decide)
  obtain ⟨hpar,ho⟩ := OddValenceSourceGeometry.source_path_parameters
    (fun i => (Reduction.P₀ L₀ S₀ i).subgroupOf G₀) hval'
    (fun q hq => hregular q hq) hodd
  refine ⟨hpar,?_⟩
  intro x y q hq hn
  rw [card_map_of_injective (G₀).subtype_injective]
  exact ho q hq hn

/-- Both literal Chapter 14 inputs on a marked coset cover: based
five-path transitivity and odd five-path fixers. The given map and endpoint
stabilizer isomorphisms are used throughout. -/
theorem original_borel_elementary_cover_path_profile_on_escaping_path
    {X : Type*} [Group X] (F₁ : Bool → Subgroup X) (f : X →* G₀)
    (cover : CoverData F₁ F₀ f) :
    BasedPathTransitive (X := X) (graph F₁) 5 ∧
      ∀ {x y : Vertex F₁} (q : (graph F₁).Walk x y), q.IsPath → q.length = 5 →
        Odd (Nat.card (pathFixer (X := X) q)) := by
  obtain ⟨_,_,_,_,hfive,hbased,_⟩ := original_borel_elementary_walk_geometry_on_escaping_path h d hc hb hcomm hbc hac Ma Mb
    g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp helem
  exact binary_graph_cover_path_profile F₀ hfive (fun q hq => hbased q hq le_rfl) F₁ f cover

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
