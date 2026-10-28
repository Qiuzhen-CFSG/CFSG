module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BetaCoreSpecial
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBetaCoreLayers

/-!
# Original beta-core special structure and full-Borel center

The exact special-group equalities transport through the injective inclusion
of the reduced completion into the original group. In particular, the image
of the full intrinsic beta-core center is the full center of the image core;
the Frattini and derived layers use the same inclusion.

Apply these equalities to the previously selected nonelementary beta branch.
Both actual U3 and SU3 quotient markings and the fixed field are retained,
as are the exact beta-center order and strict core lower bounds. At the base
edge the full original Borel two-core has center equal to the beta-center
image. Thus the special equalities in (11.8)(f) no longer remain additional
premises; the exact core order and the other (11.8) clauses still do.
The earlier local, catalogue and escaping-path inputs remain with their
existing source producers and final assembly.
Source: DGS85, Groups and Graphs (1985), reduction pp.95--96,
(11.3)(e), (11.6) and (11.8)(f), printed pp.169--176.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

private theorem centerIn_map_injective {H : Type*} [Group H]
    (R : Subgroup H) (f : H →* G) (hf : Function.Injective f) :
    (centerIn R).map f = centerIn (R.map f) := by
  rw [centerIn_eq_map_center,centerIn_eq_map_center,map_embeddedCenter R f hf]

/-- Exact special layers and the edge-core center under the original inclusion. -/
theorem original_reduced_beta_core_special_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hesc : ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (g • b)).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    let R := (Q F₀ b).map (G₀).subtype
    let C := (Z F₀ b).map (G₀).subtype
    centerIn R = C ∧ ⁅R,R⁆ = C ∧ (frattini R).map R.subtype = C ∧ C ≠ ⊥ ∧
      centerIn (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) = C := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  let htr := Reduction.reduced_triple h
  obtain ⟨hcent,hder,hphi,hnon⟩ := source_beta_core_special_on_escaping_path htr
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp
  have hedge := source_edge_core_center_on_escaping_path htr
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp
  change centerIn (Q F₀ b) = Z F₀ b at hcent
  change ⁅Q F₀ b,Q F₀ b⁆ = Z F₀ b at hder
  change (frattini (Q F₀ b)).map (Q F₀ b).subtype = Z F₀ b at hphi
  change Z F₀ b ≠ ⊥ at hnon
  change centerIn ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) = Z F₀ b at hedge
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [←centerIn_map_injective _ _ (G₀).subtype_injective,hcent]
  · rw [←map_commutator,hder]
  · rw [frattini_image_map _ _ (G₀).subtype_injective,hphi]
  · intro hh
    apply hnon
    apply map_injective (G₀).subtype_injective
    rw [Subgroup.map_bot]
    exact hh
  · rw [←centerIn_map_injective _ _ (G₀).subtype_injective,hedge]

/-- The original nonelementary edge quotient selects either unitary marking
with a special beta core and exact center, derived and Frattini layers. -/
theorem original_reduced_unitary_beta_core_special_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hesc : ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (g • b)).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ b).map (G₀).subtype).subgroupOf
        (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 ((((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) ⧸
        ((Q F₀ b).map (G₀).subtype).subgroupOf
          (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype))) :
    let qα := ((Q F₀ a).map (G₀).subtype).relIndex
      ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype)
    ∃ n, 0 < n ∧
      (ClassicalGroup.IsPSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^n) ∨
       IsSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^n)) ∧
      Nat.card ((Z F₀ b).map (G₀).subtype) = 2^n ∧
      qα^2 * 2^n < Nat.card ((Q F₀ b).map (G₀).subtype) ∧
      qα^2 < ((Z F₀ b).map (G₀).subtype).relIndex ((Q F₀ b).map (G₀).subtype) ∧
      centerIn ((Q F₀ b).map (G₀).subtype) = (Z F₀ b).map (G₀).subtype ∧
      ⁅(Q F₀ b).map (G₀).subtype,(Q F₀ b).map (G₀).subtype⁆ = (Z F₀ b).map (G₀).subtype ∧
      (frattini ((Q F₀ b).map (G₀).subtype)).map ((Q F₀ b).map (G₀).subtype).subtype =
        (Z F₀ b).map (G₀).subtype ∧
      centerIn (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) =
        (Z F₀ b).map (G₀).subtype := by
  obtain ⟨n,hn,mark,hcard,hlower,hindex⟩ := original_reduced_unitary_beta_core_bounds_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  obtain ⟨hcent,hder,hphi,_,hedge⟩ := original_reduced_beta_core_special_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  exact ⟨n,hn,mark,hcard,hlower,hindex,hcent,hder,hphi,hedge⟩

/-- The literal full-Borel branch supplies the unitary marking and special
core, and its entire two-core has the same beta-center image. -/
theorem original_borel_unitary_core_special_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {c : Vertex F₀} (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (hbc : (graph F₀).Adj (base F₀ true) c) (hac : (base F₀ false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ (base F₀ false)) (hgb : g • (base F₀ true) ≠ (base F₀ true))
    (hesc : ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤ (Q F₀ (g • (base F₀ true))).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base F₀ false) ∈ p.vertices) (hbp : (base F₀ true) ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • (base F₀ true) ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (twoCore (commonBorel L₀ S₀)))) :
    let qα := ((Q F₀ (base F₀ false)).map (G₀).subtype).relIndex
      ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ (base F₀ true)).map (G₀).subtype)
    ∃ n, 0 < n ∧
      (ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^n) ∨
      IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^n)) ∧
      Nat.card ((Z F₀ (base F₀ true)).map (G₀).subtype) = 2^n ∧
      qα^2 * 2^n < Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) ∧
      qα^2 < ((Z F₀ (base F₀ true)).map (G₀).subtype).relIndex
        ((Q F₀ (base F₀ true)).map (G₀).subtype) ∧
      centerIn ((Q F₀ (base F₀ true)).map (G₀).subtype) =
        (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      ⁅(Q F₀ (base F₀ true)).map (G₀).subtype,(Q F₀ (base F₀ true)).map (G₀).subtype⁆ =
        (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      (frattini ((Q F₀ (base F₀ true)).map (G₀).subtype)).map
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subtype = (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      centerIn (twoCore (commonBorel L₀ S₀)) = (Z F₀ (base F₀ true)).map (G₀).subtype := by
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
  obtain ⟨n,hn,mark,hcard,hlower,hindex⟩ := original_borel_unitary_core_bounds_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  obtain ⟨hcent,hder,hphi,_,hedge⟩ := original_reduced_beta_core_special_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  change centerIn (R.map (G₀).subtype) = (Z F₀ (base F₀ true)).map (G₀).subtype at hedge
  rw [hmap] at hedge
  exact ⟨n,hn,mark,hcard,hlower,hindex,hcent,hder,hphi,hedge⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
