module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryTreeRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryTreeRoots

/-!
# The common path conclusion of the two commuting Chapter 11 branches

The original beta core is relatively normal in the two-core of the full
Borel. Splitting its literal quotient into elementary and nonelementary
cases now discharges the branch hypothesis: both cases give r=4, s=5,
five-walk transitivity and odd long source-path fixers. Both original
unitary coverings are preserved in the nonelementary producer.

The actual universal-tree application supplies the two Chapter 14 path
premises without a preselected local row or an elementary-quotient premise.
The final applications construct the canonical earlier-local record using
the proved full-catalogue core obstruction. The separate rank-one catalogue
and escaping source path remain explicit: the order-144 enlargement is not
recognized by the obstruction theorem. Their discharge and complete marked
recognition remain with source assembly; this is the common path clause only.
Source: DGS85, Groups and Graphs (1985), (11.7)(f), (11.8)(g), pp.174--177,
and (14.1), p.210.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀
local notation "A" => reducedAmalgam L₀ S₀

private theorem original_beta_core_normal (h : HypothesisF11 L₀ S₀) :
    (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
      (twoCore (commonBorel L₀ S₀))).Normal := by
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
  apply normal_subgroupOf_of_le_normalizer
  rw [←hmap]
  have hn : R ≤ normalizer (Q F₀ (base F₀ true) : Set G₀) :=
    ((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Q F₀ _)
  exact (map_mono hn).trans ((Q F₀ (base F₀ true)).le_normalizer_map (G₀).subtype)

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

include h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp

/-- The common conclusion of (11.7)(f) and (11.8)(g), with the literal
full-Borel quotient branch discharged. Earlier-source premises remain explicit. -/
theorem original_borel_commuting_source_path_profile_on_escaping_path :
    HasSourcePathParameters (P := fun i => (Reduction.P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  classical
  let := original_beta_core_normal h
  by_cases helem : IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
      ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (twoCore (commonBorel L₀ S₀)))
  · obtain ⟨hs,ho⟩ := original_borel_elementary_source_path_parameters_on_escaping_path
      h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp ⟨inferInstance,helem⟩
    exact ⟨hs,original_borel_elementary_five_walk_transitive_on_escaping_path
      h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp ⟨inferInstance,helem⟩,ho⟩
  · obtain ⟨hs,ho⟩ := original_borel_unitary_source_path_parameters_on_escaping_path
      h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp ⟨inferInstance,helem⟩
    exact ⟨hs,original_borel_unitary_five_walk_transitive_on_escaping_path
      h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp ⟨inferInstance,helem⟩,ho⟩

/-- Literal Chapter 14 application on the original universal tree. No
local row or elementary/nonelementary beta branch is assumed. -/
theorem commuting_tree_path_profile_on_escaping_path :
    BasedPathTransitive (X := (A).Universal) (sourceGraph A) 5 ∧
      ∀ {x y} (q : (sourceGraph A).Walk x y), q.IsPath → q.length = 5 →
        Odd (Nat.card (pathFixer (X := (A).Universal) q)) := by
  classical
  let := original_beta_core_normal h
  by_cases helem : IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
      ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (twoCore (commonBorel L₀ S₀)))
  · exact elementary_tree_path_profile_on_escaping_path
      h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp ⟨inferInstance,helem⟩
  · exact unitary_tree_path_profile_on_escaping_path
      h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp ⟨inferInstance,helem⟩

omit d Ma Mb in
/-- Canonical source actor application: the complete earlier-local record
is constructed, while its separate rank-one quotient catalogue is retained. -/
theorem original_borel_commuting_source_path_profile_from_local_catalogue
    (Mα : IsRankOneModel ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype)))
    (Mβ : IsRankOneModel ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype))) :
    HasSourcePathParameters (P := fun i => (Reduction.P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) :=
  original_borel_commuting_source_path_profile_on_escaping_path h
    (Reduction.reducedFullEarlierLocalTheorems h) hc hb hcomm hbc hac Mα Mβ
    g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp

omit d Ma Mb in
/-- The actual Chapter 14 universal-tree path inputs with the earlier
local record and both beta-quotient branches discharged. -/
theorem commuting_tree_path_profile_from_local_catalogue
    (Mα : IsRankOneModel ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype)))
    (Mβ : IsRankOneModel ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype))) :
    BasedPathTransitive (X := (A).Universal) (sourceGraph A) 5 ∧
      ∀ {x y} (q : (sourceGraph A).Walk x y), q.IsPath → q.length = 5 →
        Odd (Nat.card (pathFixer (X := (A).Universal) q)) :=
  commuting_tree_path_profile_on_escaping_path h
    (Reduction.reducedFullEarlierLocalTheorems h) hc hb hcomm hbc hac Mα Mβ
    g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
