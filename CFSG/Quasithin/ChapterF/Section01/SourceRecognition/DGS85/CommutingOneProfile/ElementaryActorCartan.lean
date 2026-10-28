module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonbinaryElementaryActors
public import Theory.GroupTheory.CoprimeSupplementNormalizer
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootCartanCentralizer
public import Theory.GroupTheory.WeakBNPair.RegularTree.BallKernelCover

/-!
# The actual elementary apartment actor and its Cartan

The full prescribed Cartan fixes each supported path and therefore
normalizes its two half-path radicals. The proved local supplementation,
together with the Cartan's odd order, puts its intersection with the
intrinsic local group inside their join. This proves DGS (14.3)(b) with
the literal original covering map, both downstairs and upstairs.

Regularity identifies the centralizer of this two-root actor inside the
Cartan with the full midpoint neighborhood kernel. This is the two-root
calculation used in (14.5)(b); the full kernel is never replaced by O₂.
The last theorem constructs the nonbinary elementary reflections from
the source and supplies all these conclusions on their actual apartment.

This does not identify the actor core as a natural module, adjoin the
suitably chosen reflection, prove exchange or construct the Borel root
signs. Binary reflection choices, nonelementary catalogue exclusions
(including the order-144 boundary), both unitary markings and the full
original (11.7)--(11.8) marked assembly remain duties of the source family.

Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175;
(14.1)--(14.3), pp.210--212, and (14.5)(b), p.213.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

include h hc hb hcomm helem

variable (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i*t i=1)
    (htnorm : ∀ i, t i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

include c t htfix htmove htsq htnorm

variable {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=8)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t))
include hp hl hT

omit h hc hb hcomm helem htfix htmove htsq hp hl in
private theorem apartment_cartan_fixes_path : cartan c ≤ pathFixer (X := (A).Universal) p := by
  intro k hk j _
  exact reflectionApartment_fixed c t htnorm k hk _ (hT _ (p.getVert_mem_support j))

omit h hc hb hcomm helem htfix htmove htsq hp hl in
/-- The full prescribed Cartan normalizes both roots and their actual join. -/
theorem original_elementary_cartan_normalizes_actor :
    cartan c ≤ normalizer (halfPathActor (X := (A).Universal) p 4 : Set (A).Universal) := by
  intro k hk
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (pathRoot (X := (A).Universal) (p.drop 4) ⊔
    pathRoot (X := (A).Universal) (p.take 4)).map _ = _
  rw [Subgroup.map_sup]
  have hr := pathRoot_map_conj (p.drop 4) (p.drop 4) k rfl
    (fun j _ => by
      rw [drop_getVert]
      exact reflectionApartment_fixed c t htnorm k hk _ (hT _ (p.getVert_mem_support _)))
  have hl := pathRoot_map_conj (p.take 4) (p.take 4) k rfl
    (fun j _ => by
      rw [take_getVert]
      exact reflectionApartment_fixed c t htnorm k hk _ (hT _ (p.getVert_mem_support _)))
  exact congrArg₂ (fun R U : Subgroup (A).Universal => R ⊔ U) hr hl

/-- DGS (14.3)(b): the actual local Cartan is contained in the two-root
actor, both downstairs and through the original universal covering. -/
theorem original_elementary_local_cartan_le_actor :
    let D := halfPathActor (X := (A).Universal) p 4
    let J := graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4))
    ((cartan c).map (bOne_tree_map h) ⊓ J ≤ D.map (bOne_tree_map h)) ∧
      (cartan c ⊓ J.comap (bOne_tree_map h) ≤ D) := by
  intro D J
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hactors⟩ :=
    original_elementary_apartment_actor_quotients h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  obtain ⟨_,_,_,hcover,_⟩ := hactors p hp hl hT
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hn := original_elementary_cartan_normalizes_actor c t htnorm p hT
  have hnm : (cartan c).map (bOne_tree_map h) ≤ normalizer (D.map (bOne_tree_map h) : Set G₀) :=
    (map_mono hn).trans (D.le_normalizer_map (bOne_tree_map h))
  have hcov : D.map (bOne_tree_map h) ⊔ J.pCoreIn 2=J := by
    have hJ : J.pCoreIn 2=Q F ((bOne_tree_cover h).vertex (p.getVert 4)) := sylowGenerated_core _
    rw [hJ]
    exact hcover
  have hle := coprime_normalizer_inf_le_pCore_supplement
    (halfPathActor_map_le_local h p 4 hl) hcov hnm
    ((cartan_odd c).of_dvd_right ((cartan c).card_map_dvd (bOne_tree_map h)))
  refine ⟨hle,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := hle ⟨mem_map_of_mem (bOne_tree_map h) hx.1,hx.2⟩
  have hxv : x • p.getVert 4=p.getVert 4 :=
    apartment_cartan_fixes_path c t htnorm p hT hx.1 4 (by omega)
  have hyv : y • p.getVert 4=p.getVert 4 := halfPathActor_le_midpoint_stabilizer hl hy
  have he := (bOne_tree_cover h).stabilizerEquiv (p.getVert 4) |>.injective
    (a₁ := ⟨y,hyv⟩) (a₂ := ⟨x,hxv⟩) (Subtype.ext hxy)
  have hyx : y=x := congrArg Subtype.val he
  exact hyx ▸ hy

/-- The two-root centralizer calculation for DGS (14.5)(b), with the full
original local permutation kernel. -/
theorem original_elementary_cartan_actor_centralizer :
    cartan c ⊓ centralizer (halfPathActor (X := (A).Universal) p 4 : Set (A).Universal) =
      cartan c ⊓ (U F ((bOne_tree_cover h).vertex (p.getVert 4))).comap (bOne_tree_map h) := by
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  let l := p.take 4
  let r := (p.drop 4).reverse
  have hll : l.length=4 := by simp only [l,take_length,hl]; decide
  have hrl : r.length=4 := by simp only [r,length_reverse,drop_length,hl]
  have hlnil : ¬l.Nil := by intro hh; have := hh.length_eq_zero; omega
  have hrnil : ¬r.Nil := by intro hh; have := hh.length_eq_zero; omega
  have hprevl : l.penultimate=p.getVert 3 := by
    simp only [penultimate,hll,l,take_getVert]; rfl
  have hprevr : r.penultimate=p.getVert 5 := by
    simp only [penultimate,hrl,r,getVert_reverse,drop_length,hl,drop_getVert]
  have hdiff : l.penultimate≠r.penultimate := by
    rw [hprevl,hprevr]
    intro he
    have := hp.getVert_injOn (by omega : 3≤p.length) (by omega : 5≤p.length) he
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
    fun k hk => reflectionApartment_fixed c t htnorm k hk z hz
  have hfac (u v) (q : (sourceGraph A).Walk u v) (hqpos : 0<q.length)
      (hqT : ∀ z∈q.support, z∈cartanApartment A (reflectionGroup c t)) :=
    apartment_path_factorization h c 4 (by decide) t htfix htmove htsq
      htnorm hpath.1 (original_source_tree_thickness h t) q hqpos hqT
  have hnewr : r.penultimate∉l.support := by
    intro hm
    exact hdiff.symm (htree.eq_penultimate_of_adj_end (hp.take 4) (r.adj_penultimate hrnil).symm hm)
  have hnewl : l.penultimate∉r.support := by
    intro hm
    exact hdiff (htree.eq_penultimate_of_adj_end (hp.drop 4).reverse (l.adj_penultimate hlnil).symm hm)
  have hoddp := hpath.2 (l.concat (r.adj_penultimate hrnil).symm)
    ((hp.take 4).concat hnewr _) (by rw [length_concat,hll])
  have hoddq := hpath.2 (r.concat (l.adj_penultimate hlnil).symm)
    ((hp.drop 4).reverse.concat hnewl _) (by rw [length_concat,hrl])
  have hleft (k) (hk : k∈cartan c) := pathRoot_commute_iff_fixes_neighbors htree (source_action A)
    l (hp.take 4) (by rw [hll]; exact hpath.1) (cartan c)
    (apartment_cartan_fixes_path c t htnorm l hTl) (r.adj_penultimate hrnil).symm hdiff.symm
    (hK _ (hTr _ (r.getVert_mem_support _))) (hfac _ _ l (by omega) hTl) hoddp k hk
  have hright (k) (hk : k∈cartan c) := pathRoot_commute_iff_fixes_neighbors htree (source_action A)
    r (hp.drop 4).reverse (by rw [hrl]; exact hpath.1) (cartan c)
    (apartment_cartan_fixes_path c t htnorm r hTr) (l.adj_penultimate hlnil).symm hdiff
    (hK _ (hTl _ (l.getVert_mem_support _))) (hfac _ _ r (by omega) hTr) hoddq k hk
  ext k
  constructor
  · rintro ⟨hk,hc⟩
    refine ⟨hk,?_⟩
    have hs : ∀ z, (sourceGraph A).Adj (p.getVert 4) z → k • z=z :=
      (hleft k hk).mp (fun x hx => (mem_centralizer_iff.mp hc x ((show pathRoot (X := (A).Universal) l ≤ halfPathActor (X := (A).Universal) p 4 from le_sup_right) hx)).symm)
    intro w hw
    rcases (Subgroup.CosetGeometry.RankTwo.mem_ball_one F _ w).mp hw with hw | rfl
    · obtain ⟨u,hu⟩ := ((bOne_tree_cover h).neighbor_bijective (p.getVert 4)).2 ⟨w,hw⟩
      have he : (bOne_tree_cover h).vertex u.val=w := congrArg Subtype.val hu
      rw [←he,←(bOne_tree_cover h).vertex_smul,hs u.val u.property]
    · rw [←(bOne_tree_cover h).vertex_smul]
      exact congrArg (bOne_tree_cover h).vertex
        (apartment_cartan_fixes_path c t htnorm p hT hk 4 (by omega))
  · rintro ⟨hk,hU⟩
    have hkv : k • p.getVert 4=p.getVert 4 :=
      apartment_cartan_fixes_path c t htnorm p hT hk 4 (by omega)
    have hs : ∀ z, (sourceGraph A).Adj (p.getVert 4) z → k • z=z := by
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
    have hc : halfPathActor (X := (A).Universal) p 4 ≤ centralizer ({k} : Set (A).Universal) := by
      dsimp only [r] at hcr
      rw [pathRoot_reverse] at hcr
      exact sup_le hcr hcl
    exact ⟨hk,mem_centralizer_iff.mpr (fun x hx =>
      (mem_centralizer_iff.mp (hc hx) k (Set.mem_singleton k)).symm)⟩



omit c t htfix htmove htsq htnorm hp hl hT p in
/-- The nonbinary elementary source supplies the same-Cartan reflections and
all local Cartan containment and two-root centralizer identities, without
catalogue or reflection assumptions. -/
theorem original_elementary_nonbinary_actor_cartan_control
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i = base T i) ∧
      (∀ i, t i • base T (!i) ≠ base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan (chosenCartans h) : Set (A).Universal)) ∧
    ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=8 →
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup (chosenCartans h) t)) →
      let D := halfPathActor (X := (A).Universal) p 4
      let J := graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4))
      cartan (chosenCartans h) ≤ normalizer (D : Set (A).Universal) ∧
      ((cartan (chosenCartans h)).map (bOne_tree_map h) ⊓ J ≤ D.map (bOne_tree_map h)) ∧
      (cartan (chosenCartans h) ⊓ J.comap (bOne_tree_map h) ≤ D) ∧
      cartan (chosenCartans h) ⊓ centralizer (D : Set (A).Universal) =
        cartan (chosenCartans h) ⊓
          (U F ((bOne_tree_cover h).vertex (p.getVert 4))).comap (bOne_tree_map h) := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb (chosenCartans h)
  refine ⟨t,htfix,htmove,htsq,htnorm,?_⟩
  intro a b p hp hl hT D J
  have hcontain := original_elementary_local_cartan_le_actor h hc hb hcomm helem
    (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT
  exact ⟨original_elementary_cartan_normalizes_actor (chosenCartans h) t htnorm p hT,
    hcontain.1,hcontain.2,original_elementary_cartan_actor_centralizer h hc
      hb hcomm helem (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
