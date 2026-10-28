module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorQuotient
public import Theory.GroupTheory.CoprimeSupplementNormalizer
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootCartanCentralizer
public import Theory.GroupTheory.WeakBNPair.RegularTree.BallKernelCover

/-!
# Cartan control on the strict half-path actor

The two actual six-path radicals are normalized by the prescribed Cartan.
Their proved supplementation of the midpoint two-core then puts the intrinsic
Cartan in their join. Regularity identifies its Cartan centralizer with the
full midpoint neighborhood kernel, retaining the original covering map.
These are the (14.3)(b) and (14.5)(b) inputs to the kernel analysis in (14.9).
They do not identify the actor's two-core with the source Z_i.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(14.3)(b), p.212, (14.5)(b), p.213, and (14.9)(c), pp.215--216.
The argument also follows the existing four-path calculation in
`CommutingOneProfile/ElementaryActorCartan`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
variable {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b) (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection))

include hT in
private theorem cartan_fixes_path : cartan c ≤ pathFixer (X := (A).Universal) p := by
  intro k hk j _
  exact reflectionApartment_fixed c d.reflection d.normalizes k hk _ (hT _ (p.getVert_mem_support j))

include hT in
/-- The full prescribed Cartan normalizes both roots and their actual join. -/
theorem six_cartan_normalizes_actor :
    cartan c ≤ normalizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal) := by
  intro k hk
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (pathRoot (X := (A).Universal) (p.drop 6) ⊔
    pathRoot (X := (A).Universal) (p.take 6)).map _ = _
  rw [Subgroup.map_sup]
  have hr := pathRoot_map_conj (p.drop 6) (p.drop 6) k rfl
    (fun j _ => by
      rw [drop_getVert]
      exact reflectionApartment_fixed c d.reflection d.normalizes k hk _ (hT _ (p.getVert_mem_support _)))
  have hl := pathRoot_map_conj (p.take 6) (p.take 6) k rfl
    (fun j _ => by
      rw [take_getVert]
      exact reflectionApartment_fixed c d.reflection d.normalizes k hk _ (hT _ (p.getVert_mem_support _)))
  exact congrArg₂ (fun R U : Subgroup (A).Universal => R ⊔ U) hr hl

include hl hT in
/-- DGS (14.3)(b): the actual local Cartan is contained in the two-root
actor, both downstairs and through the original universal covering. -/
theorem six_local_cartan_le_actor
    (hcover : (halfPathActor (X := (reducedAmalgam L S).Universal) p 6).map (bOne_tree_map h) ⊔
      Q (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) =
        graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6))) :
    let D := halfPathActor (X := (A).Universal) p 6
    let J := graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6))
    ((cartan c).map (bOne_tree_map h) ⊓ J ≤ D.map (bOne_tree_map h)) ∧
      (cartan c ⊓ J.comap (bOne_tree_map h) ≤ D) := by
  intro D J
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hn := six_cartan_normalizes_actor c d p hT
  have hnm : (cartan c).map (bOne_tree_map h) ≤ normalizer (D.map (bOne_tree_map h) : Set G₀) :=
    (map_mono hn).trans (D.le_normalizer_map (bOne_tree_map h))
  have hcov : D.map (bOne_tree_map h) ⊔ J.pCoreIn 2=J := by
    have hJ : J.pCoreIn 2=Q F ((bOne_tree_cover h).vertex (p.getVert 6)) := sylowGenerated_core _
    rw [hJ]
    exact hcover
  have hle := coprime_normalizer_inf_le_pCore_supplement
    (halfPathActor_map_le_local h p 6 hl) hcov hnm
    ((cartan_odd c).of_dvd_right ((cartan c).card_map_dvd (bOne_tree_map h)))
  refine ⟨hle,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := hle ⟨mem_map_of_mem (bOne_tree_map h) hx.1,hx.2⟩
  have hxv : x • p.getVert 6=p.getVert 6 :=
    cartan_fixes_path c d p hT hx.1 6 (by omega)
  have hyv : y • p.getVert 6=p.getVert 6 := halfPathActor_le_midpoint_stabilizer hl hy
  have he := (bOne_tree_cover h).stabilizerEquiv (p.getVert 6) |>.injective
    (a₁ := ⟨y,hyv⟩) (a₂ := ⟨x,hxv⟩) (Subtype.ext hxy)
  have hyx : y=x := congrArg Subtype.val he
  exact hyx ▸ hy

include hp hl hT in
/-- The two-root centralizer calculation for DGS (14.5)(b), with the full
original local permutation kernel. -/
theorem six_cartan_actor_centralizer :
    cartan c ⊓ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal) =
      cartan c ⊓ (U F ((bOne_tree_cover h).vertex (p.getVert 6))).comap (bOne_tree_map h) := by
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
  have hTl : ∀ z∈l.support, z∈cartanApartment A (reflectionGroup c d.reflection) := by
    intro z hz
    rw [support_take] at hz
    exact hT z (List.mem_of_mem_take hz)
  have hTr : ∀ z∈r.support, z∈cartanApartment A (reflectionGroup c d.reflection) := by
    intro z hz
    simp only [r,support_reverse,List.mem_reverse] at hz
    rw [drop_support_eq_support_drop_min] at hz
    exact hT z (List.mem_of_mem_drop hz)
  have hK (z) (hz : z∈cartanApartment A (reflectionGroup c d.reflection)) :
      ∀ k∈cartan c, k • z=z :=
    fun k hk => reflectionApartment_fixed c d.reflection d.normalizes k hk z hz
  have hfac (u v) (q : (sourceGraph A).Walk u v) (hqpos : 0<q.length)
      (hqT : ∀ z∈q.support, z∈cartanApartment A (reflectionGroup c d.reflection)) :=
    apartment_path_factorization h c 6 (by decide) d.reflection d.fixes d.moves d.squares
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
    (cartan_fixes_path c d l hTl) (r.adj_penultimate hrnil).symm hdiff.symm
    (hK _ (hTr _ (r.getVert_mem_support _))) (hfac _ _ l (by omega) hTl) hoddp k hk
  have hright (k) (hk : k∈cartan c) := pathRoot_commute_iff_fixes_neighbors htree (source_action A)
    r (hp.drop 6).reverse (by rw [hrl]; exact d.transitive) (cartan c)
    (cartan_fixes_path c d r hTr) (l.adj_penultimate hlnil).symm hdiff
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
        (cartan_fixes_path c d p hT hk 6 (by omega))
  · rintro ⟨hk,hU⟩
    have hkv : k • p.getVert 6=p.getVert 6 :=
      cartan_fixes_path c d p hT hk 6 (by omega)
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

end CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
