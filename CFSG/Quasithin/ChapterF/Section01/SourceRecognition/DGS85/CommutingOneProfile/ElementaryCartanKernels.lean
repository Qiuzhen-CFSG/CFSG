module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorTorus
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryRootCoordinates
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootCartanTransitivity
public import Theory.GroupTheory.AbelianRootNormalizer

/-!
# The elementary Cartan's full local-kernel factors

The single-root centralizer is the full midpoint permutation kernel inside
the Cartan. The intrinsic Cartan is transitive on nonidentity root elements;
commutativity then decomposes the full Cartan into its actor part and that
kernel. In nonbinary local quotients the two factors are disjoint and the
kernel has the exact complementary order. No actor faithfulness is assumed.

At a beta midpoint the neighboring alpha torus has order q_beta squared
minus one, strictly greater than q_beta minus one. Thus the beta kernel
is nontrivial. This also covers q_beta=2 when reflections are supplied.
ElementaryBetaExchange constructs those reflections in the nonbinary source
and applies the result to exchange and the literal marked comparison.
The alpha kernel, root signs, binary choices, nonelementary catalogue
exclusions and full original 11.7/11.8 assembly remain source obligations.

Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175, and
(14.5)(b)--(14.6), pp.213--214. The kernel is G_v^(1), not O_2(G_v).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
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
private theorem cartan_fixes_path : cartan c ≤ pathFixer (X := (A).Universal) p := by
  intro k hk j _
  exact reflectionApartment_fixed c t htnorm k hk _ (hT _ (p.getVert_mem_support j))

/-- The single-root form of DGS (14.5)(b), with the full neighborhood kernel. -/
theorem original_elementary_single_root_cartan_centralizer :
    cartan c ⊓ centralizer (pathRoot (X := (A).Universal) (p.drop 4) : Set (A).Universal) =
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
  have hnewl : l.penultimate∉r.support := by
    intro hm
    exact hdiff (htree.eq_penultimate_of_adj_end (hp.drop 4).reverse (l.adj_penultimate hlnil).symm hm)
  have hoddq := hpath.2 (r.concat (l.adj_penultimate hlnil).symm)
    ((hp.drop 4).reverse.concat hnewl _) (by rw [length_concat,hrl])
  have hright (k) (hk : k∈cartan c) := pathRoot_commute_iff_fixes_neighbors htree (source_action A)
    r (hp.drop 4).reverse (by rw [hrl]; exact hpath.1) (cartan c)
    (cartan_fixes_path c t htnorm r hTr) (l.adj_penultimate hlnil).symm hdiff
    (hK _ (hTl _ (l.getVert_mem_support _))) (hfac _ _ r (by omega) hTr) hoddq k hk
  ext k
  constructor
  · rintro ⟨hk,hc⟩
    refine ⟨hk,?_⟩
    have hs : ∀ z, (sourceGraph A).Adj (p.getVert 4) z → k • z=z := by
      apply (hright k hk).mp
      intro x hx
      have hx' : x∈pathRoot (X := (A).Universal) (p.drop 4) := by
        simpa only [r,pathRoot_reverse] using hx
      exact (mem_centralizer_iff.mp hc x hx').symm
    intro w hw
    rcases (Subgroup.CosetGeometry.RankTwo.mem_ball_one F _ w).mp hw with hw | rfl
    · obtain ⟨u,hu⟩ := ((bOne_tree_cover h).neighbor_bijective (p.getVert 4)).2 ⟨w,hw⟩
      have he : (bOne_tree_cover h).vertex u.val=w := congrArg Subtype.val hu
      rw [←he,←(bOne_tree_cover h).vertex_smul,hs u.val u.property]
    · rw [←(bOne_tree_cover h).vertex_smul]
      exact congrArg (bOne_tree_cover h).vertex
        (cartan_fixes_path c t htnorm p hT hk 4 (by omega))
  · rintro ⟨hk,hU⟩
    have hkv : k • p.getVert 4=p.getVert 4 :=
      cartan_fixes_path c t htnorm p hT hk 4 (by omega)
    have hs : ∀ z, (sourceGraph A).Adj (p.getVert 4) z → k • z=z := by
      intro z hz
      exact (bOne_tree_cover h).fixes_neighbor_of_image hz k hkv
        (hU _ ((Subgroup.CosetGeometry.RankTwo.mem_ball_one F _ _).mpr (Or.inl ((bOne_tree_cover h).hom.map_adj hz))))
    refine ⟨hk,mem_centralizer_iff.mpr ?_⟩
    intro x hx
    have hx' : x∈pathRoot (X := (A).Universal) r := by
      change x∈pathRoot (X := (A).Universal) (p.drop 4) at hx
      simpa only [r,pathRoot_reverse] using hx
    exact ((hright k hk).mpr hs x hx').symm.eq

/-- The intrinsic part of the full Cartan is transitive on nonidentity
four-path root elements, without a faithful-actor or Cartan-kernel premise. -/
theorem original_elementary_root_cartan_transitive
    (x y : (A).Universal)
    (hx : x∈pathRoot (X := (A).Universal) (p.drop 4))
    (hy : y∈pathRoot (X := (A).Universal) (p.drop 4))
    (hxn : x≠1) (hyn : y≠1) :
    ∃ k∈cartan c ⊓ halfPathActor (X := (A).Universal) p 4, k*x*k⁻¹=y := by
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hroots⟩ :=
    original_elementary_apartment_root_coordinates h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  let D := halfPathActor (X := (A).Universal) p 4
  let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
  let C := (cartan c).subgroupOf D
  let v := (bOne_tree_cover h).vertex (p.getVert 4)
  obtain ⟨hf,hker,hr,hv,z,hR,hV,_⟩ := hroots p hp hl hT
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 4 hl (e v))
  have hdis : R ⊓ f.ker=⊥ := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective,hker]
    exact hr
  have hn : C ≤ normalizer (R : Set D) := by
    intro k hk
    have hfix : k.val∈pathFixer (X := (A).Universal) (p.drop 4) := by
      intro j _
      rw [drop_getVert]
      exact reflectionApartment_fixed c t htnorm k.val hk _ (hT _ (p.getVert_mem_support _))
    exact (pathRoot (X := (A).Universal) (p.drop 4)).le_normalizer_comap D.subtype
      (pathFixer_le_normalizer_pathRoot (p.drop 4) hfix)
  have hdiag := original_elementary_actor_full_diagonal h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT (e v) z hR hV
  have hRD : pathRoot (X := (A).Universal) (p.drop 4) ≤ D := le_sup_left
  obtain ⟨k,hk,he⟩ := NaturalCubic.upper_root_cartan_transitive f R C hdis hn hR hdiag
    ⟨x,hRD hx⟩ ⟨y,hRD hy⟩ hx hy
    (fun hh => hxn (congrArg Subtype.val hh)) (fun hh => hyn (congrArg Subtype.val hh))
  exact ⟨k,⟨hk,k.property⟩,congrArg D.subtype he⟩


omit hc hb hcomm helem htfix htmove htsq hp in
/-- Both local tori inside the same original full Cartan have their exact
orders. The adjacent fields and literal midpoint quotient marks are retained. -/
theorem original_elementary_adjacent_cartan_orders
    {k l : Type*} [Field k] [Finite k] [CharP k 2]
    [Field l] [Finite l] [CharP l 2]
    (ev : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)))) ≃* SL(2,k))
    (ew : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 5)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 5)))) ≃* SL(2,l)) :
    let C₀ := (cartan c).map (bOne_tree_map h)
    Nat.card (C₀ ⊓ graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)) : Subgroup G₀)=Nat.card k-1 ∧
      Nat.card (C₀ ⊓ graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 5)) : Subgroup G₀)=Nat.card l-1 := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 4)
  let w := cov.vertex (p.getVert 5)
  let C₀ := (cartan c).map φ
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  dsimp only
  have hvw : (graph F).Adj v w := cov.hom.map_adj (p.adj_getVert_succ (by omega))
  have hCE : C₀ ≤ stabilizer F v ⊓ stabilizer F w := by
    rintro _ ⟨x,hx,rfl⟩
    constructor
    · change φ x • cov.vertex (p.getVert 4)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm x hx _
        (hT _ (p.getVert_mem_support 4))]
    · change φ x • cov.vertex (p.getVert 5)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm x hx _
        (hT _ (p.getVert_mem_support 5))]
  let E := F false ⊓ F true
  let W := (twoGroup L S).map φ
  have hmapE : (originalMiddle A).map φ=E := by
    rw [show originalMiddle A=T false ⊓ T true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact cov.map_inf
  have hC0 : C₀ ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hW0 : W ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hWn : E ≤ normalizer (W : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hWcore : W ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hW0 hWn
  have ho : Odd (Nat.card C₀) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hd0 : Disjoint C₀ (E.pCoreIn 2) := by
    obtain ⟨r,hr⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hg0 : C₀ ⊔ E.pCoreIn 2=E := by
    apply le_antisymm (sup_le hC0 (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    exact he.symm.le.trans (sup_le (hWcore.trans le_sup_right) le_sup_left)
  have hEbase : E=stabilizer F (base F false) ⊓ stabilizer F (base F true) := by
    rw [show stabilizer F (base F false)=F false from Subgroup.CosetGeometry.stabilizer_base F false,
      show stabilizer F (base F true)=F true from Subgroup.CosetGeometry.stabilizer_base F true]
  have hbase : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨hd,hg⟩ := CommutingTrivial.path_cartan_complement_at_edge (reduced_triple h)
    hbase hvw C₀ (hEbase ▸ hC0) hCE ho (hEbase ▸ hd0) (hEbase ▸ hg0)
  obtain ⟨⟨etor⟩,_⟩ := CommutingTrivial.edge_complement_local_torus (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw ev C₀ hCE hd hg
  obtain ⟨⟨etor'⟩,_⟩ := CommutingTrivial.edge_complement_local_torus (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw.symm ew C₀
    (fun x hx => ⟨(hCE hx).2,(hCE hx).1⟩) (by rw [inf_comm (stabilizer F w) (stabilizer F v)]; exact hd)
    (by rw [inf_comm (stabilizer F w) (stabilizer F v)]; exact hg)
  exact ⟨(Nat.card_congr etor.toEquiv).trans (Nat.card_units (α := k)),
    (Nat.card_congr etor'.toEquiv).trans (Nat.card_units (α := l))⟩

/-- The full Cartan splits as its actual actor part times its full local
kernel part; this holds before the actor's two-core has been eliminated. -/
theorem original_elementary_cartan_kernel_factorization :
    cartan c = (cartan c ⊓ halfPathActor (X := (A).Universal) p 4) ⊔
      (cartan c ⊓ (U F ((bOne_tree_cover h).vertex (p.getVert 4))).comap (bOne_tree_map h)) := by
  let _ := cartan_abelian h c
  let R := pathRoot (X := (A).Universal) (p.drop 4)
  have hn : cartan c ≤ normalizer (R : Set (A).Universal) := by
    apply le_trans ?_ (pathFixer_le_normalizer_pathRoot (p.drop 4))
    intro k hk j _
    rw [drop_getVert]
    exact reflectionApartment_fixed c t htnorm k hk _ (hT _ (p.getVert_mem_support _))
  have hne : R≠⊥ := by
    obtain ⟨m,hm,K,fK,finK,chK,hK,e,hroots⟩ :=
      original_elementary_apartment_root_coordinates h hc hb hcomm helem
        c t htfix htmove htsq htnorm
    let _ := fK
    let _ := finK
    let _ := chK
    obtain ⟨_,_,_,_,z,hR,_⟩ := hroots p hp hl hT
    intro he
    change ((R.subgroupOf _).map _) = _ at hR
    rw [he,Subgroup.bot_subgroupOf,Subgroup.map_bot] at hR
    have hh := congrArg (fun W : Subgroup SL(2,K ((bOne_tree_cover h).vertex (p.getVert 4)).type) => Nat.card W) hR
    rw [Subgroup.card_bot,
      Matrix.SpecialLinearGroup.card_upperUnipotent] at hh
    exact (Finite.one_lt_card (α := K ((bOne_tree_cover h).vertex (p.getVert 4)).type)).ne' hh.symm
  have hf := abelian_normalizer_eq_sup_root_centralizer (cartan c)
    (cartan c ⊓ halfPathActor (X := (A).Universal) p 4) R inf_le_left hn hne
    (fun x hx y hy hx1 hy1 => original_elementary_root_cartan_transitive
      h hc hb hcomm helem c t htfix htmove htsq htnorm p hp hl hT x y hx hy hx1 hy1)
  rw [show cartan c ⊓ centralizer (R : Set (A).Universal) = _ from
    original_elementary_single_root_cartan_centralizer h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT] at hf
  exact hf


/-- In a nonbinary local quotient the two Cartan factors are disjoint,
and the full local-kernel factor has the exact complementary order. -/
theorem original_elementary_cartan_kernel_card
    {k l : Type*} [Field k] [Finite k] [CharP k 2]
    [Field l] [Finite l] [CharP l 2]
    (ev : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)))) ≃* SL(2,k))
    (ew : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 5)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 5)))) ≃* SL(2,l))
    (hk : 4≤Nat.card k) :
    let C₀ := (cartan c).map (bOne_tree_map h)
    let v := (bOne_tree_cover h).vertex (p.getVert 4)
    C₀ = (C₀ ⊓ graphLocalGroup F v) ⊔ (C₀ ⊓ U F v) ∧
      Disjoint (C₀ ⊓ graphLocalGroup F v) (C₀ ⊓ U F v) ∧
      Nat.card C₀ = (Nat.card k-1) * Nat.card (C₀ ⊓ U F v : Subgroup G₀) := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 4)
  let w := cov.vertex (p.getVert 5)
  let C₀ := (cartan c).map φ
  let D := halfPathActor (X := (A).Universal) p 4
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C₀ := inferInstance
  dsimp only
  have hvw : (graph F).Adj v w := cov.hom.map_adj
    (p.adj_getVert_succ (show 4<p.length by omega))
  have ho : Odd (Nat.card C₀) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  have hgen : C₀=(C₀ ⊓ graphLocalGroup F v) ⊔ (C₀ ⊓ U F v) := by
    apply le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    have he := congrArg (Subgroup.map φ)
      (original_elementary_cartan_kernel_factorization h hc hb hcomm helem
        c t htfix htmove htsq htnorm p hp hl hT)
    rw [Subgroup.map_sup] at he
    change C₀=_ at he
    apply he.le.trans
    apply sup_le
    · rintro _ ⟨x,hx,rfl⟩
      exact (show C₀ ⊓ graphLocalGroup F v ≤ (C₀ ⊓ graphLocalGroup F v) ⊔ (C₀ ⊓ U F v) from le_sup_left)
        ⟨mem_map_of_mem φ hx.1,halfPathActor_map_le_local h p 4 hl (mem_map_of_mem φ hx.2)⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact (show C₀ ⊓ U F v ≤ (C₀ ⊓ graphLocalGroup F v) ⊔ (C₀ ⊓ U F v) from le_sup_right)
        ⟨mem_map_of_mem φ hx.1,hx.2⟩
  have hdis : Disjoint (C₀ ⊓ graphLocalGroup F v) (C₀ ⊓ U F v) :=
    (CommutingTrivial.nonbinary_odd_torus_disjoint_kernel (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw ev hk C₀ ho).mono_right inf_le_right
  have hn : C₀ ⊓ U F v ≤ normalizer (C₀ ⊓ graphLocalGroup F v : Set G₀) :=
    inf_le_left.trans ((C₀.le_centralizer.trans (centralizer_le
      (show C₀ ⊓ graphLocalGroup F v ≤ C₀ from inf_le_left))).trans (Subgroup.centralizer_le_normalizer _))
  have hc0 := (original_elementary_adjacent_cartan_orders h c t htnorm p hl hT ev ew).1
  refine ⟨hgen,hdis,?_⟩
  calc
    Nat.card C₀ = Nat.card ((C₀ ⊓ graphLocalGroup F v) ⊔ (C₀ ⊓ U F v) : Subgroup G₀) :=
      congrArg (fun W : Subgroup G₀ => Nat.card W) hgen
    _ = Nat.card (C₀ ⊓ graphLocalGroup F v : Subgroup G₀) * Nat.card (C₀ ⊓ U F v : Subgroup G₀) :=
      card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hdis
    _ = _ := by rw [hc0]

/-- At a beta midpoint the neighboring alpha torus is strictly larger,
so the full Cartan has a nontrivial full local-kernel factor. This also
holds in the binary case whenever the displayed apartment is given. -/
theorem original_elementary_beta_cartan_kernel_ne_bot
    (hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type=true) :
    (cartan c).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥ := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 4)
  let w := cov.vertex (p.getVert 5)
  change v.type=true at hv
  let C₀ := (cartan c).map φ
  let D := halfPathActor (X := (A).Universal) p 4
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hfix : cartan c ≤ MulAction.stabilizer (A).Universal (p.getVert 4) := by
    intro k hk
    exact cartan_fixes_path c t htnorm p hT hk 4 (by omega)
  have hC0v : C₀ ≤ stabilizer F v := by
    rintro _ ⟨k,hk,rfl⟩
    change φ k • cov.vertex (p.getVert 4)=_
    rw [←cov.vertex_smul,hfix hk]
  let _ : Finite C₀ := Finite.of_injective (inclusion hC0v) (inclusion_injective _)
  have hφC (x : (A).Universal) (hx : x∈cartan c) (he : φ x=1) : x=1 := by
    have hh := cov.stabilizerEquiv (p.getVert 4) |>.injective
      (a₁ := ⟨x,hfix hx⟩) (a₂ := 1) (Subtype.ext (by change φ x=φ 1; simpa only [map_one] using he))
    exact congrArg Subtype.val hh
  intro hzero
  have hzero' : cartan c ⊓ (U F v).comap φ=⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply hφC x hx.1
    exact mem_bot.mp (hzero ▸ ⟨mem_map_of_mem φ hx.1,hx.2⟩)
  have hCD : cartan c ≤ D := by
    have hf := original_elementary_cartan_kernel_factorization h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT
    rw [hzero',sup_bot_eq] at hf
    exact hf.le.trans inf_le_right
  have hC0J : C₀ ≤ graphLocalGroup F v :=
    (map_mono hCD).trans (halfPathActor_map_le_local h p 4 hl)
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,_⟩ :=
    original_elementary_apartment_actor_quotients h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨hc0,hc1⟩ := original_elementary_adjacent_cartan_orders h c t htnorm p hl hT (e v) (e w)
  have hw : w.type=false := by
    have hh := (cov.hom.map_adj (p.adj_getVert_succ (show 4<p.length by omega))).1
    change v.type≠w.type at hh
    cases hw : w.type
    · rfl
    · exact (hh (hv.trans hw.symm)).elim
  have hc0' : Nat.card C₀=2^m-1 := by
    rw [inf_eq_left.mpr hC0J] at hc0
    simpa only [hK,hv,ite_true] using hc0
  have hc1' : Nat.card (C₀ ⊓ graphLocalGroup F w : Subgroup G₀)=2^(2*m)-1 := by
    simpa only [hK,hw,Bool.false_eq_true,ite_false] using hc1
  have hle : 2^(2*m)-1≤2^m-1 := by
    rw [←hc0',←hc1']
    exact Nat.card_le_card_of_injective (inclusion (show C₀ ⊓ graphLocalGroup F w ≤ C₀ from inf_le_left))
      (inclusion_injective _)
  have hpow : 2^m<2^(2*m) := Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
  have hpos : 0<2^m := pow_pos (by decide) _
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
