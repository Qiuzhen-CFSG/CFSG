module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryMarkedPathFixers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryPathParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryTreeRoots

/-!
# The original unitary four- and five-walk profiles

The alpha field supplied by the source marking applies the independently
proved odd five-walk fixer theorem. The edge two-core has order 2^(10m),
exactly the number of five-walks extending an edge with the marked valences.
Its action is free because the fixers are odd, and counting makes it
transitive. Restriction gives four-walk transitivity at every vertex.

This proves source r=4, s=5 with its closed-path convention. The actual
universal-cover map transports both Chapter 14 inputs. The original graph
need not be a tree. The source hypotheses, alpha catalogue, PSU/SU marking
and every positive field degree are retained; no initial path profile is
assumed. OriginalUnitarySource re-exports these results and preserves its
historical signatures as compatibility wrappers.
Source: DGS85, Groups and Graphs, (11.8)(g), pp.176--177; (14.1), p.210.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory.AmalgamGraph
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree Theory.GroupAction.CubicTree
open SimpleGraph.Walk
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀
local notation "Amalgam₀" => reducedAmalgam L₀ S₀

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

/-- Every original nonbacktracking walk of length at least five has odd fixer. -/
theorem original_unitary_long_walk_fixer_odd_from_marking
    {x y : Vertex F₀} (q : (graph F₀).Walk x y) (hlen : 5 ≤ q.length)
    (hnb : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) :
    Odd (Nat.card (pathFixer (X := G₀) q)) := by
  let d := reducedFullEarlierLocalTheorems h
  let a := base F₀ false
  let b := base F₀ true
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ :=
    original_unitary_escaping_four_walk h hc hb hcomm Ma hm mark

  let eL := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have mark' : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) := by
    rcases mark with hh | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
    · exact Or.inl (hh.of_mulEquiv eqb)
    · exact Or.inr ⟨E,inferInstance,inferInstance,J,hcard,hconj,⟨eqb.trans e⟩⟩
  obtain ⟨k,_,_,hk,⟨ea₀⟩⟩ := (original_unitary_centers_and_field h hc hb hcomm Ma hm mark).2.2.2
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let ea := ea₀.trans ep.symm
  have hlen5 : (q.take 5).length = 5 := by rw [take_length,Nat.min_eq_left hlen]
  have hnb5 : ∀ i, i+2 ≤ (q.take 5).length →
      (q.take 5).getVert i ≠ (q.take 5).getVert (i+2) := by
    intro i hi
    rw [hlen5] at hi
    simpa only [take_getVert,Nat.min_eq_right (show i ≤ 5 by omega),
      Nat.min_eq_right (show i+2 ≤ 5 by omega)] using hnb i (by omega)
  have ho : Odd (Nat.card (pathFixer (X := G₀) (q.take 5))) :=
    source_unitary_five_walk_fixer_odd_from_marking
    (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
    (Reduction.reduced_vertex_sylow h) d hc hb hcomm hbc hac (Ma.of_equiv eqa) hm mark' (eqa.trans ea) hk (q.take 5) hlen5 hnb5
  let := finite_endpoints (Reduction.reduced_triple h)
  apply Odd.of_dvd_nat ho
  apply card_dvd_of_le
  intro x hx i hi
  rw [take_getVert]
  exact hx _ (Nat.min_le_left _ _ |>.trans hlen)

/-- The marked valences, five-walk transitivity and odd long-walk fixers,
with all earlier path premises discharged. -/
theorem original_unitary_walk_geometry_from_marking :
    (∀ x : Vertex F₀, Nat.card ((graph F₀).neighborSet x) =
      2^(if x.type then 3*m else 2*m)+1) ∧
    (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
    (∀ {n : ℕ} {x : Vertex F₀} (q : BasedWalk (graph F₀) n x),
      q.Nonbacktracking → 5 ≤ n → Odd (Nat.card (pathStabilizer F₀ q))) ∧
    ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), 5 ≤ q.length →
      (∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) →
        Odd (Nat.card (pathFixer (X := G₀) q)) := by
  have hS := (original_borel_unitary_core_orders_from_marking h hc hb hcomm Ma hm mark).2.1
  have hval := (original_unitary_field_and_valences h hc hb hcomm Ma hm mark).2
  have hodd {x y : Vertex F₀} (q : (graph F₀).Walk x y) (hlen : 5 ≤ q.length)
      (hnb : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) :
      Odd (Nat.card (pathFixer (X := G₀) q)) :=
    original_unitary_long_walk_fixer_odd_from_marking h hc hb hcomm Ma hm mark q hlen hnb
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
  have hbase : Nat.card ((F₀ false ⊓ F₀ true).pCoreIn 2) = 2^(10*m) := by
    simpa only [R,Subgroup.CosetGeometry.stabilizer_base] using hS
  have hcard {x y : Vertex F₀} (hxy : (graph F₀).Adj x y) :
      Nat.card ((stabilizer F₀ x ⊓ stabilizer F₀ y).pCoreIn 2) = 2^(10*m) := by
    obtain ⟨t,ht⟩ := edgeStabilizer_map_base F₀ hxy
    rw [ht,Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj t).injective,card_map_of_injective (MulAut.conj t).injective,hbase]
  refine ⟨hval,?_,hbased,hodd⟩
  apply two_power_graph_five_walk_transitive_of_edge_cores F₀ (fun i => if i then 3*m else 2*m) hval
  · intro x y hxy
    simpa only [Bool.false_eq_true,if_false,if_true,show 2*(2*m+3*m) = 10*m by omega] using hcard hxy
  · intro x q hq
    exact hbased q hq le_rfl

/-- Four-walk transitivity at every original vertex; in particular this supplies
the former alpha-orbit input to the original source profiles. -/
theorem original_unitary_four_walk_transitive_from_marking (x : Vertex F₀) :
    RootPathTransitive (graph F₀) G₀ x 4 := by
  obtain ⟨hval,hfive,_⟩ := original_unitary_walk_geometry_from_marking h hc hb hcomm Ma hm mark
  have hdeg : BasedWalk.HasTwoNeighbors (graph F₀) := by
    intro a b
    exact Set.exists_ne_of_one_lt_ncard (s := (graph F₀).neighborSet a) (by
      rw [←Nat.card_coe_set_eq,hval]
      have := pow_pos (by decide : 0 < (2:ℕ)) (if a.type then 3*m else 2*m)
      omega) b
  exact (hfive x).mono hdeg (by decide)

/-- Source (11.8)(g), including closed source paths and the literal fixer
images in the original group, without an initial path-transitivity premise. -/
theorem original_borel_unitary_source_path_profile_from_marking :
    HasSourcePathParameters (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  obtain ⟨hval,hfive,hbased,hodd⟩ :=
    original_unitary_walk_geometry_from_marking h hc hb hcomm Ma hm mark
  have hpos : ∀ i : Bool, 0 < (if i then 3*m else 2*m) := by intro i; cases i <;> simp <;> omega
  have hregular {n : ℕ} {x : Vertex F₀} (q : BasedWalk (graph F₀) n x)
      (hq : q.Nonbacktracking) : Regular (A := G₀) q ↔ n ≤ 4 :=
    two_power_graph_regular_iff_of_five_transitive F₀
      (fun i => if i then 3*m else 2*m) hpos hval hfive (fun q hq hn => hbased q hq hn) q hq
  have hval' (x : Vertex F₀) : 3 ≤ Nat.card ((graph F₀).neighborSet x) ∧
      Odd (Nat.card ((graph F₀).neighborSet x)) := by
    rw [hval]
    have hgt : 1 < 2^(if x.type then 3*m else 2*m) := one_lt_pow₀ (by decide) (by
      have := hpos x.type; omega)
    refine ⟨by omega,?_⟩
    exact Even.add_odd ((by decide : Even (2:ℕ)).pow_of_ne_zero (by
      have := hpos x.type; omega)) (by decide)
  obtain ⟨hpar,ho⟩ := OddValenceSourceGeometry.source_path_parameters
    (fun i => (Reduction.P₀ L₀ S₀ i).subgroupOf G₀) hval'
    (fun q hq => hregular q hq) hodd
  refine ⟨hpar,hfive,?_⟩
  intro x y q hq hn
  rw [card_map_of_injective (G₀).subtype_injective]
  exact ho q hq hn

/-- Both Chapter 14 path inputs on the original full-Borel universal tree. -/
theorem original_unitary_tree_path_profile_from_marking :
    BasedPathTransitive (X := (Amalgam₀).Universal) (sourceGraph Amalgam₀) 5 ∧
      ∀ {x y} (q : (sourceGraph Amalgam₀).Walk x y), q.IsPath → q.length = 5 →
        Odd (Nat.card (pathFixer (X := (Amalgam₀).Universal) q)) := by
  obtain ⟨_,hfive,hbased,_⟩ :=
    original_unitary_walk_geometry_from_marking h hc hb hcomm Ma hm mark
  exact binary_graph_cover_path_profile F₀ hfive (fun q hq => hbased q hq le_rfl)
    (Universal.cosetFamily Amalgam₀) (NoncommutingProfile.bOne_tree_map h)
    (NoncommutingProfile.bOne_tree_cover h)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
