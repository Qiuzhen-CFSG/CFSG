module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FullElementaryMarkedProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalElementaryFiniteQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorQuotient

/-!
# Actual opposite-root actors in the elementary Chapter 11 apartment

The original full-Borel elementary branch constructs both local fields and
markings. On every supported eight-path, its two four-path radicals have
distinct Sylow images in the same midpoint SL₂ quotient, and generate that
quotient. Restricting the original covering and local quotient gives a
surjective homomorphism with kernel exactly the actor's own two-core.
The quotient equivalence retains its formula on every representative, and
the two roots supplement the original midpoint core.

NonbinaryElementaryActors supplies the actual source consumer, constructing
its Cartan involutions and apartment without a reflection premise. Neither
local catalogue, field, quotient map nor root generation is assumed here. The binary reflection
choice, nonelementary catalogues, exchange, root signs and complete marked
recognition remain separate obligations.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175;
(14.1)--(14.3)(a), pp.210--212.
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

private theorem elementary_fixed_field_markings :
    ∃ m, 0 < m ∧ ∃ (K : Bool → Type) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Finite (K i)) (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i) = 2^(if i then m else 2*m)) ∧
      ∀ v : Vertex F, Nonempty
        ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type)) := by
  obtain ⟨m,hm,markB,markA,_⟩ :=
    original_borel_elementary_orders_and_paths_of_source h hc hb hcomm helem
  obtain ⟨k₀,f₀,fin₀,h₀,⟨e₀⟩⟩ := markA
  obtain ⟨k₁,f₁,fin₁,h₁,⟨e₁⟩⟩ := markB
  let _ := f₀
  let _ := fin₀
  let _ := f₁
  let _ := fin₁
  let _ : Fintype k₀ := Fintype.ofFinite k₀
  let _ : Fintype k₁ := Fintype.ofFinite k₁
  let _ : CharP k₀ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₀)
  let _ : CharP k₁ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₁)
  let K : Bool → Type := fun i => if i then k₁ else k₀
  let _ : ∀ i, Field (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, Finite (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, CharP (K i) 2 := fun i => by cases i <;> assumption
  let eOrig : ∀ i, ((graphLocalGroup F (base F i)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F (base F i)).map (G₀).subtype)) ≃* PSL(2,K i) := by
    intro i
    cases i
    · exact e₀
    · exact e₁
  let eBase (i : Bool) : (graphLocalGroup F (base F i) ⧸
      pCore 2 (graphLocalGroup F (base F i))) ≃* SL(2,K i) :=
    let j := (graphLocalGroup F (base F i)).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
    (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans ((eOrig i).trans
      (MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm)
  refine ⟨m,hm,K,inferInstance,inferInstance,inferInstance,?_,
    fun v => ⟨source_linear_quotient_at (reduced_triple h) K eBase v⟩⟩
  intro i
  cases i
  · exact h₀
  · exact h₁

variable (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i*t i=1)
    (htnorm : ∀ i, t i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

include c t htfix htmove htsq htnorm

private theorem elementary_four_actor_surjective
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hlen : p.length=8)
    (hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c t))
    (e : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)))) ≃* SL(2,k))
    (hval : Nat.card ((sourceGraph A).neighborSet (p.getVert 4)) = Nat.card k+1) :
    Function.Surjective (halfPathLinearMap h p 4 hlen e) := by
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have hthick := original_source_tree_thickness h t
  let l := p.take 4
  let r := (p.drop 4).reverse
  have hl : l.length=4 := by simp only [l,take_length,hlen]; decide
  have hr : r.length=4 := by simp only [r,length_reverse,drop_length,hlen]
  have hlnil : ¬l.Nil := by intro hh; have := hh.length_eq_zero; omega
  have hrnil : ¬r.Nil := by intro hh; have := hh.length_eq_zero; omega
  have hprevl : l.penultimate=p.getVert 3 := by
    simp only [penultimate,hl,l,take_getVert]; rfl
  have hprevr : r.penultimate=p.getVert 5 := by
    simp only [penultimate,hr,r,getVert_reverse,drop_length,hlen,drop_getVert]
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
      htnorm hpath.1 hthick q hqpos hqT
  have : Finite ((sourceGraph A).neighborSet (p.getVert 4)) :=
    Nat.finite_of_card_ne_zero (by rw [hval]; omega)
  have hnewr : r.penultimate∉l.support := by
    intro hm
    exact hdiff.symm (htree.eq_penultimate_of_adj_end (hp.take 4) (r.adj_penultimate hrnil).symm hm)
  have hnewl : l.penultimate∉r.support := by
    intro hm
    exact hdiff (htree.eq_penultimate_of_adj_end (hp.drop 4).reverse (l.adj_penultimate hlnil).symm hm)
  have hoddp := hpath.2 (l.concat (r.adj_penultimate hrnil).symm)
    ((hp.take 4).concat hnewr _) (by rw [length_concat,hl])
  have hoddq := hpath.2 (r.concat (l.adj_penultimate hlnil).symm)
    ((hp.drop 4).reverse.concat hnewl _) (by rw [length_concat,hr])
  have hjoin : pathRoot (X := (A).Universal) l ⊔ pathRoot (X := (A).Universal) r =
      halfPathActor (X := (A).Universal) p 4 := by
    dsimp only [r]
    rw [pathRoot_reverse,sup_comm]
  let j := MulEquiv.subgroupCongr hjoin
  let f := (halfPathLinearMap h p 4 hlen e).comp j.toMonoidHom
  have hf : Function.Surjective f :=
    opposite_pathRoots_linear_surjective htree (source_action A)
      l r (hp.take 4) (hp.drop 4).reverse hlnil hrnil hdiff hval
      (by rw [hl]; exact hpath.1) (by rw [hr]; exact hpath.1) (cartan c)
      (hK _ (hTl _ (l.getVert_mem_support _))) (hK _ (hTr _ (r.getVert_mem_support _)))
      (hfac _ _ l (by omega) hTl) (hfac _ _ r (by omega) hTr) hoddp hoddq f
      (fun x hx w hw => halfPathLinearMap_kernel_fixes_neighbors h p 4 hlen e (j x) hx w hw)
  exact Function.Surjective.of_comp hf


/-- DGS (14.3)(a) for the actual elementary four-path roots. Only the
same-Cartan reflections remain primitive geometric inputs; both catalogues,
fields, path actions, exact kernel and literal quotient marking are derived. -/
theorem original_elementary_apartment_actor_quotients :
    ∃ m, 0 < m ∧ ∃ (K : Bool → Type) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Finite (K i)) (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i) = 2^(if i then m else 2*m)) ∧
    ∃ e : ∀ v : Vertex F,
      (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type),
    ∀ {a b} (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=8),
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c t)) →
      Function.Surjective (halfPathLinearMap h p 4 hl
        (e ((bOne_tree_cover h).vertex (p.getVert 4)))) ∧
      (halfPathLinearMap h p 4 hl (e ((bOne_tree_cover h).vertex (p.getVert 4)))).ker =
        pCore 2 (halfPathActor (X := (A).Universal) p 4) ∧
      (halfPathActor (X := (A).Universal) p 4).pCoreIn 2 ≤
        (MulAction.stabilizer (A).Universal (p.getVert 4)).pCoreIn 2 ∧
      (halfPathActor (X := (A).Universal) p 4).map (bOne_tree_map h) ⊔
        Q F ((bOne_tree_cover h).vertex (p.getVert 4)) =
          graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)) ∧
      ∃ E : (halfPathActor (X := (A).Universal) p 4 ⧸
          pCore 2 (halfPathActor (X := (A).Universal) p 4)) ≃*
            SL(2,K ((bOne_tree_cover h).vertex (p.getVert 4)).type),
        ∀ x : halfPathActor (X := (A).Universal) p 4,
          E (QuotientGroup.mk' _ x) = e _ (QuotientGroup.mk' _ (halfPathLocalMap h p 4 hl x)) := by
  obtain ⟨m,hm,K,fK,finK,chK,hK,e'⟩ := elementary_fixed_field_markings h hc hb hcomm helem
  let _ := fK
  let _ := finK
  let _ := chK
  let e (v) := Classical.choice (e' v)
  refine ⟨m,hm,K,fK,finK,chK,hK,e,?_⟩
  have hi (i : Bool) : ((F (!i)).subgroupOf (F i)).index = Nat.card (K i)+1 := by
    have hadj : (graph F).Adj (base F i) (base F (!i)) :=
      ⟨by change i≠!i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
    have he := source_linear_edge_index_of_quotient (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hadj (e (base F i))
    change (stabilizer F (base F (!i))).relIndex (stabilizer F (base F i)) = _ at he
    rw [show stabilizer F (base F i) = F i from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F (base F (!i)) = F (!i) from Subgroup.CosetGeometry.stabilizer_base _ _] at he
    exact he
  have hval (v : SourceVertex A) :
      Nat.card ((sourceGraph A).neighborSet v) =
        Nat.card (K ((bOne_tree_cover h).vertex v).type)+1 := by
    rw [Nat.card_congr (Equiv.ofBijective ((bOne_tree_cover h).hom.mapNeighborSet v)
      ((bOne_tree_cover h).neighbor_bijective v))]
    exact card_neighbors_of_indices F (fun i => Nat.card (K i)+1) hi _
  intro a b p hp hl hT
  let J := graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4))
  let D := halfPathActor (X := (A).Universal) p 4
  let f := halfPathLinearMap h p 4 hl (e ((bOne_tree_cover h).vertex (p.getVert 4)))
  have hf : Function.Surjective f := elementary_four_actor_surjective h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT (e _) (hval _)
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 4 hl)
  have hker : f.ker = pCore 2 D := by
    have hh := f.comap_pCore_of_ker_isPGroup hf (halfPathLinearMap_kernel_isTwo h p 4 hl (e _))
    simpa only [Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot,MonoidHom.comap_bot] using hh
  have hcore : D.pCoreIn 2 ≤ (MulAction.stabilizer (A).Universal (p.getVert 4)).pCoreIn 2 := by
    apply universal_two_subgroup_le_core_of_neighbors h (p.getVert 4) _
      (isPGroup_pCoreIn 2 _) ((pCoreIn_le 2 _).trans (halfPathActor_le_midpoint_stabilizer hl))
    rintro x ⟨y,hy,rfl⟩ w hw
    exact halfPathLinearMap_kernel_fixes_neighbors h p 4 hl (e _) y (hker.symm ▸ hy) w hw
  have hsupp : D.map (bOne_tree_map h) ⊔ Q F ((bOne_tree_cover h).vertex (p.getVert 4)) = J := by
    let j := halfPathLocalMap h p 4 hl
    let q := QuotientGroup.mk' (pCore 2 J)
    have hsurj : Function.Surjective (q.comp j) := by
      intro z
      obtain ⟨x,hx⟩ := hf (e _ z)
      exact ⟨x,(e _).injective hx⟩
    have hmap : j.range.map q = q.range := by
      rw [←MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hsurj,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    have hs : j.range ⊔ pCore 2 J = ⊤ := by
      have hh := (Subgroup.map_eq_range_iff.mp hmap).eq_top
      simpa only [q,QuotientGroup.ker_mk'] using hh
    have hh := congrArg (Subgroup.map J.subtype) hs
    have he : J.subtype.comp j = (bOne_tree_map h).comp D.subtype := rfl
    rw [Subgroup.map_sup,←MonoidHom.range_comp,he,MonoidHom.range_comp,range_subtype,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    have hJ : (pCore 2 J).map J.subtype = Q F ((bOne_tree_cover h).vertex (p.getVert 4)) :=
      sylowGenerated_core _
    rwa [hJ] at hh
  let E : (D ⧸ pCore 2 D) ≃* SL(2,K ((bOne_tree_cover h).vertex (p.getVert 4)).type) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨hf,hker,hcore,hsupp,E,fun _ => rfl⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
