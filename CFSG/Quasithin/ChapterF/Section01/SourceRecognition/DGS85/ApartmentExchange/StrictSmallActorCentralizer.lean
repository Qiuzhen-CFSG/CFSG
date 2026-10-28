module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorCartan
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootCartanCentralizer
public import Theory.GroupTheory.WeakBNPair.RegularTree.BallKernelCover

/-!
# The strict two-root actor and the full local permutation kernel

The Cartan centralizer of the actual two half-path radicals is its
intersection with the full midpoint neighborhood kernel. Path transitivity,
odd seven-path fixers and the original covering prove both inclusions.
This is the literal source calculation of DGS (14.5)(b), retaining U rather
than replacing the whole local kernel by its two-core. No apartment exchange,
natural core action, or reduced model comparison is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
variable (h : HypothesisF11 L S)

private theorem six_actor_cartan_centralizer
    (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hl : p.length = 12)
    (hT : ∀ z ∈ p.support, z ∈ cartanApartment A (reflectionGroup c d.reflection)) :
    cartan c ⊓ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal) =
      cartan c ⊓ (U F ((bOne_tree_cover h).vertex (p.getVert 6))).comap (bOne_tree_map h) := by
  let t := d.reflection
  have fix_path {x y : SourceVertex A} (q : (sourceGraph A).Walk x y)
      (hq : ∀ z ∈ q.support, z ∈ cartanApartment A (reflectionGroup c t)) :
      cartan c ≤ pathFixer (X := (A).Universal) q := by
    intro k hk j _
    exact reflectionApartment_fixed c t d.normalizes k hk _ (hq _ (q.getVert_mem_support j))
  let l := p.take 6
  let r := (p.drop 6).reverse
  have hll : l.length=6 := by simp only [l,take_length,hl]; decide
  have hrl : r.length=6 := by simp only [r,length_reverse,drop_length,hl]
  have hlnil : ¬l.Nil := by intro hh; have := hh.length_eq_zero; omega
  have hrnil : ¬r.Nil := by intro hh; have := hh.length_eq_zero; omega
  have hprevl : l.penultimate=p.getVert 5 := by
    simp only [penultimate,hll,l,take_getVert]; rfl
  have hprevr : r.penultimate=p.getVert 7 := by
    simp only [penultimate,hrl,r,getVert_reverse,drop_length,hl,drop_getVert]
  have hdiff : l.penultimate≠r.penultimate := by
    rw [hprevl,hprevr]
    intro he
    have := hp.getVert_injOn (by omega : 5≤p.length) (by omega : 7≤p.length) he
    omega
  have htree := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hTl : ∀ z∈l.support, z∈cartanApartment A (reflectionGroup c t) := by
    intro z hz
    rw [support_take] at hz
    exact hT z (List.mem_of_mem_take hz)
  have hTr : ∀ z∈r.support, z∈cartanApartment A (reflectionGroup c t) := by
    intro z hz
    simp only [r,support_reverse,List.mem_reverse] at hz
    rw [drop_support_eq_support_drop_min] at hz
    exact hT z (List.mem_of_mem_drop hz)
  have hK (z) (hz : z∈cartanApartment A (reflectionGroup c t)) :
      ∀ k∈cartan c, k • z=z :=
    fun k hk => reflectionApartment_fixed c t d.normalizes k hk z hz
  have hfac (u v) (q : (sourceGraph A).Walk u v) (hqpos : 0<q.length)
      (hqT : ∀ z∈q.support, z∈cartanApartment A (reflectionGroup c t)) :=
    apartment_path_factorization h c 6 (by decide) t d.fixes d.moves d.squares
      d.normalizes d.transitive d.thick q hqpos hqT
  have hnewr : r.penultimate∉l.support := by
    intro hm
    exact hdiff.symm (htree.eq_penultimate_of_adj_end (hp.take 6) (r.adj_penultimate hrnil).symm hm)
  have hnewl : l.penultimate∉r.support := by
    intro hm
    exact hdiff (htree.eq_penultimate_of_adj_end (hp.drop 6).reverse (l.adj_penultimate hlnil).symm hm)
  have hoddp := d.odd (l.concat (r.adj_penultimate hrnil).symm)
    ((hp.take 6).concat hnewr _) (by rw [length_concat,hll])
  have hoddq := d.odd (r.concat (l.adj_penultimate hlnil).symm)
    ((hp.drop 6).reverse.concat hnewl _) (by rw [length_concat,hrl])
  have hleft (k) (hk : k∈cartan c) := pathRoot_commute_iff_fixes_neighbors htree (source_action A)
    l (hp.take 6) (by rw [hll]; exact d.transitive) (cartan c)
    (fix_path l hTl) (r.adj_penultimate hrnil).symm hdiff.symm
    (hK _ (hTr _ (r.getVert_mem_support _))) (hfac _ _ l (by omega) hTl) hoddp k hk
  have hright (k) (hk : k∈cartan c) := pathRoot_commute_iff_fixes_neighbors htree (source_action A)
    r (hp.drop 6).reverse (by rw [hrl]; exact d.transitive) (cartan c)
    (fix_path r hTr) (l.adj_penultimate hlnil).symm hdiff
    (hK _ (hTl _ (l.getVert_mem_support _))) (hfac _ _ r (by omega) hTr) hoddq k hk
  ext k
  constructor
  · rintro ⟨hk,hc⟩
    refine ⟨hk,?_⟩
    have hs : ∀ z, (sourceGraph A).Adj (p.getVert 6) z → k • z=z :=
      (hleft k hk).mp (fun x hx => (mem_centralizer_iff.mp hc x ((show pathRoot (X := (A).Universal) l ≤ halfPathActor (X := (A).Universal) p 6 from le_sup_right) hx)).symm)
    intro w hw
    rcases (Subgroup.CosetGeometry.RankTwo.mem_ball_one F _ w).mp hw with hw | rfl
    · obtain ⟨u,hu⟩ := ((bOne_tree_cover h).neighbor_bijective (p.getVert 6)).2 ⟨w,hw⟩
      have he : (bOne_tree_cover h).vertex u.val=w := congrArg Subtype.val hu
      rw [←he,←(bOne_tree_cover h).vertex_smul,hs u.val u.property]
    · rw [←(bOne_tree_cover h).vertex_smul]
      exact congrArg (bOne_tree_cover h).vertex
        (fix_path p hT hk 6 (by omega))
  · rintro ⟨hk,hU⟩
    have hkv : k • p.getVert 6=p.getVert 6 :=
      fix_path p hT hk 6 (by omega)
    have hs : ∀ z, (sourceGraph A).Adj (p.getVert 6) z → k • z=z := by
      intro z hz
      exact (bOne_tree_cover h).fixes_neighbor_of_image hz k hkv
        (hU _ ((Subgroup.CosetGeometry.RankTwo.mem_ball_one F _ _).mpr (Or.inl ((bOne_tree_cover h).hom.map_adj hz))))
    have hcl : pathRoot (X := (A).Universal) l ≤ centralizer ({k} : Set (A).Universal) := by
      intro x hx
      exact mem_centralizer_iff.mpr (fun y hy => by
        have he : y=k := Set.mem_singleton_iff.mp hy
        rw [he]
        exact ((hleft k hk).mpr hs x hx).eq)
    have hcr : pathRoot (X := (A).Universal) r ≤ centralizer ({k} : Set (A).Universal) := by
      intro x hx
      exact mem_centralizer_iff.mpr (fun y hy => by
        have he : y=k := Set.mem_singleton_iff.mp hy
        rw [he]
        exact ((hright k hk).mpr hs x hx).eq)
    have hc : halfPathActor (X := (A).Universal) p 6 ≤ centralizer ({k} : Set (A).Universal) := by
      dsimp only [r] at hcr
      rw [pathRoot_reverse] at hcr
      exact sup_le hcr hcl
    exact ⟨hk,mem_centralizer_iff.mpr (fun x hx =>
      (mem_centralizer_iff.mp (hc hx) k (Set.mem_singleton k)).symm)⟩

variable {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

/-- The full local permutation kernel is detected by centralizing the two
actual half-path radicals in the original source-selected Cartan. -/
theorem strict_source_small_actor_cartan_centralizer
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length = 12)
    (hT : ∀ z ∈ p.support,
      z ∈ strictSourceApartment h hc hne hb hβu hns hlinear) :
    cartan (chosenCartans h) ⊓ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal) =
      cartan (chosenCartans h) ⊓
        (U F ((bOne_tree_cover h).vertex (p.getVert 6))).comap (bOne_tree_map h) :=
  six_actor_cartan_centralizer h (chosenCartans h)
    (strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear) p hp hl hT

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
