module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryCoreProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedUnitaryPathFixers
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRootCover

/-!
# Unitary path roots and the marked-cover fixer premise

The nonelementary quotient of the full original Borel selects a positive
unitary field degree and either the projective or special unitary cover.
The proved long-walk theorem then gives odd fixers without adding a natural
module or fixed-space premise. On a four-path, the actual two-core therefore
acts freely at every new exit; the statement retains its literal image in
the original completion.

For a supplied marked coset cover, the original covering homomorphism
induces an isomorphism of the complete pointwise fixers. Local injectivity
preserves nonbacktracking even when the image path closes. Thus every
five-path in that cover has odd fixer. This is the actual odd-fixer input
of the regular-apartment argument. Five-walk transitivity, the exact
parameters r=4 and s=5, and the remaining earlier-source discharge are
retained obligations, not consequences asserted by this module.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.8)(g), printed pp.176--177, and (14.1), printed p.210.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon SimpleGraph.Walk
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The original nonelementary branch gives odd long-walk fixers and the
actual free action of each four-path radical at every new exit. -/
theorem original_borel_unitary_path_roots_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {c : Vertex F₀} (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (hbc : (graph F₀).Adj (base F₀ true) c) (hac : (base F₀ false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ (base F₀ false))
    (hgb : g • (base F₀ true) ≠ (base F₀ true))
    (hesc : ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤
      (Q F₀ (g • (base F₀ true))).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base F₀ false) ∈ p.vertices) (hbp : (base F₀ true) ∈ p.vertices)
    (hcp : c ∈ p.vertices) (hgbp : g • (base F₀ true) ∈ p.vertices)
    (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
          (twoCore (commonBorel L₀ S₀)))) :
    (∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y),
      (∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype))) ∧
    ∀ {x y z : Vertex F₀} (q : (graph F₀).Walk x y), q.IsPath → q.length = 4 →
      (h : (graph F₀).Adj y z) → z ∉ q.support →
        (pathRoot (X := G₀) q).map (G₀).subtype ⊓ (stabilizer F₀ z).map (G₀).subtype = ⊥ ∧
        Function.Injective (fun t : pathRoot (X := G₀) q => (t : G₀) • z) := by
  obtain ⟨m,hm,mark,_⟩ := original_borel_unitary_beta_profile_on_escaping_path h d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  have hodd {x y : Vertex F₀} (q : (graph F₀).Walk x y) (hl : 5 ≤ q.length)
      (hn : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) :
      Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) :=
    original_borel_unitary_long_walk_fixer_odd_on_escaping_path h d hc hb hcomm
      hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne m hm mark q hl hn
  refine ⟨fun q hn hl => hodd q hl hn,?_⟩
  intro x y z q hq hlen hyz hnew
  have hq' := hq.concat hnew hyz
  have ho := hodd (q.concat hyz) (by rw [length_concat,hlen]) (by
    intro i hi he
    have hh := hq'.getVert_injOn (by omega : i ≤ (q.concat hyz).length) hi he
    omega)
  rw [card_map_of_injective (G₀).subtype_injective] at ho
  refine ⟨?_,pathRoot_smul_injective q hyz ho⟩
  rw [←Subgroup.map_inf _ _ _ (G₀).subtype_injective,
    pathRoot_inf_stabilizer_eq_bot q hyz ho,Subgroup.map_bot]

private theorem cover_fixer_card
    {X Y : Type*} [Group X] [Group Y] {F : Bool → Subgroup X} {E : Bool → Subgroup Y}
    {f : X →* Y} (c : CoverData F E f) {a b : Vertex F} (q : (graph F).Walk a b) :
    Nat.card (pathFixer (X := X) q) = Nat.card (pathFixer (X := Y) (q.map c.hom)) := by
  let φ : pathFixer (X := X) q →* pathFixer (X := Y) (q.map c.hom) :=
    { toFun := fun t => ⟨f t, by rw [←c.pathFixer_map q]; exact mem_map_of_mem f t.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun t u => Subtype.ext (map_mul f (t : X) (u : X)) }
  apply Nat.card_congr (MulEquiv.ofBijective φ ?_).toEquiv
  constructor
  · intro t u he
    have ht : (t : X) ∈ stabilizer F a := by
      change (t : X) • a = a
      simpa only [getVert_zero] using t.property 0 (Nat.zero_le _)
    have hu : (u : X) ∈ stabilizer F a := by
      change (u : X) • a = a
      simpa only [getVert_zero] using u.property 0 (Nat.zero_le _)
    have he' : f (t : X) = f (u : X) :=
      congrArg (fun v : pathFixer (X := Y) (q.map c.hom) => (v : Y)) he
    have hh : c.stabilizerHom a ⟨t,ht⟩ = c.stabilizerHom a ⟨u,hu⟩ := Subtype.ext he'
    exact Subtype.ext (congrArg (fun v : stabilizer F a => (v : X))
      ((c.stabilizerHom_bijective a).1 hh))
  · intro t
    have ht : (t : Y) ∈ (pathFixer (X := X) q).map f := by
      rw [c.pathFixer_map q]
      exact t.property
    obtain ⟨u,hu,he⟩ := ht
    exact ⟨⟨u,hu⟩,Subtype.ext he⟩

/-- The literal odd-five-path premise on any supplied marked coset cover.
This is the fixer input to the regular-apartment argument; its independent
five-path transitivity premise is not asserted here. -/
theorem original_borel_unitary_cover_five_path_fixer_odd_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {c : Vertex F₀} (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (hbc : (graph F₀).Adj (base F₀ true) c) (hac : (base F₀ false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ (base F₀ false))
    (hgb : g • (base F₀ true) ≠ (base F₀ true))
    (hesc : ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤
      (Q F₀ (g • (base F₀ true))).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base F₀ false) ∈ p.vertices) (hbp : (base F₀ true) ∈ p.vertices)
    (hcp : c ∈ p.vertices) (hgbp : g • (base F₀ true) ∈ p.vertices)
    (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
          (twoCore (commonBorel L₀ S₀))))
    {X : Type*} [Group X] (F₁ : Bool → Subgroup X) (f : X →* G₀)
    (cover : CoverData F₁ F₀ f)
    {x y : Vertex F₁} (q : (graph F₁).Walk x y) (hq : q.IsPath) (hlen : q.length = 5) :
    Odd (Nat.card (pathFixer (X := X) q)) := by
  have ho := (original_borel_unitary_path_roots_on_escaping_path h d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne).1 (q.map cover.hom) (by
    intro i hi he
    rw [length_map] at hi
    rw [getVert_map,getVert_map] at he
    have h₀ := q.adj_getVert_succ (by omega : i < q.length)
    have h₁ := q.adj_getVert_succ (by omega : i+1 < q.length)
    have hi' : q.getVert i = q.getVert (i+2) := congrArg Subtype.val
      ((cover.neighbor_bijective (q.getVert (i+1))).1
        (a₁ := ⟨q.getVert i,h₀.symm⟩) (a₂ := ⟨q.getVert (i+2),h₁⟩) (Subtype.ext he))
    have hbad := hq.getVert_injOn (by omega : i ≤ q.length) hi hi'
    omega) (by rw [length_map,hlen])
  rw [card_map_of_injective (G₀).subtype_injective] at ho
  rwa [cover_fixer_card cover q]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
