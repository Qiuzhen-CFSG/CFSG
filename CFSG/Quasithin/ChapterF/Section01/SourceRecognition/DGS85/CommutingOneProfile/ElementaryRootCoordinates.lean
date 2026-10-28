module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonbinaryElementaryActors
public import Theory.SpecificGroups.SL2.OppositeSylowMarking

/-!
# Simultaneous coordinates on the actual elementary apartment roots

On each length-eight apartment path, odd five-path fixers make both
four-path radicals disjoint from the kernel of the original midpoint
quotient. Their regular exit actions give the field-sized orders. Thus
their images are two distinct full Sylows, and one inner change of the
original SL2 marking sends them to all upper and lower transvections.
The quotient is still the literal local map composed with this marking;
its kernel is the actor's own two-core.

Reciprocal root parameters lift to actual involutions whose product has
cube in that same core. This supplies the root-image and involution inputs
of the Chapter 14 cubic argument. It does not assert that the cube itself
is trivial, that the kernel is natural, or that exchange holds. The last
theorem constructs the Cartan reflections from the nonbinary elementary
source, so no catalogue, reflection or root-coordinate premise remains in
that application. Binary reflection choices, nonelementary exclusions,
Cartan/core control, exchange, root signs and full marked recognition
remain separate duties of this source family.

Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175;
(14.1)--(14.3)(a), pp.210--212, and (14.12)--(14.13), pp.217--218.
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

private theorem elementary_four_root_coordinates
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hlen : p.length=8)
    (hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c t))
    (e : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)))) ≃* SL(2,k)) :
    Nat.card ((sourceGraph A).neighborSet (p.getVert 4)) = Nat.card k+1 →
    let D := halfPathActor (X := (A).Universal) p 4
    let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
    let U := (pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D
    let f := halfPathLinearMap h p 4 hlen e
    R ⊓ f.ker=⊥ ∧ U ⊓ f.ker=⊥ ∧
      ∃ z : SL(2,k),
        R.map ((MulAut.conj z).toMonoidHom.comp f)=Matrix.SpecialLinearGroup.upperUnipotent k ∧
        ∀ y : SL(2,k), y∈U.map ((MulAut.conj z).toMonoidHom.comp f) ↔
          ∃ a : k, Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero a=y := by
  intro hval D R U f
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
  let R' := (pathRoot (X := (A).Universal) r).subgroupOf D
  have hR : R'=R := by dsimp only [R',R,r]; rw [pathRoot_reverse]
  have hRle : pathRoot (X := (A).Universal) r ≤ D := by
    dsimp only [r]
    rw [pathRoot_reverse]
    exact le_sup_left
  have hcR : Nat.card R'=Nat.card k := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRle).toEquiv]
    have hh := card_pathRoot_add_one htree (source_action A) r (hp.drop 4).reverse hrnil
      (by rw [hr]; exact hpath.1) (cartan c)
      ⟨l.penultimate,(l.adj_penultimate hlnil).symm,hdiff⟩
      (hK _ (hTl _ (l.getVert_mem_support _))) (hfac _ _ r (by omega) hTr) hoddq
    exact Nat.add_right_cancel (hh.trans hval)
  have hcU : Nat.card U=Nat.card k := by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show pathRoot (X := (A).Universal) l ≤ D from le_sup_right)).toEquiv]
    have hh := card_pathRoot_add_one htree (source_action A) l (hp.take 4) hlnil
      (by rw [hl]; exact hpath.1) (cartan c)
      ⟨r.penultimate,(r.adj_penultimate hrnil).symm,hdiff.symm⟩
      (hK _ (hTr _ (r.getVert_mem_support _))) (hfac _ _ l (by omega) hTl) hoddp
    exact Nat.add_right_cancel (hh.trans hval)
  have hrk : R' ⊓ f.ker=⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hh : (x:(A).Universal)∈pathRoot (X := (A).Universal) r ⊓
        MulAction.stabilizer (A).Universal l.penultimate :=
      ⟨hx.1,halfPathLinearMap_kernel_fixes_neighbors h p 4 hlen e x hx.2 _
        (l.adj_penultimate hlnil).symm⟩
    rwa [pathRoot_inf_stabilizer_eq_bot r _ hoddq] at hh
  have huk : U ⊓ f.ker=⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hh : (x:(A).Universal)∈pathRoot (X := (A).Universal) l ⊓
        MulAction.stabilizer (A).Universal r.penultimate :=
      ⟨hx.1,halfPathLinearMap_kernel_fixes_neighbors h p 4 hlen e x hx.2 _
        (r.adj_penultimate hrnil).symm⟩
    rwa [pathRoot_inf_stabilizer_eq_bot l _ hoddp] at hh
  have hne : R'.map f≠U.map f := by
    intro he
    have hc : 1<Nat.card R' := by
      rw [hcR]
      let _ : Fintype k := Fintype.ofFinite k
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hrne : R'≠⊥ := by intro hh; rw [hh,card_bot] at hc; omega
    obtain ⟨x,hx,hxne⟩ := R'.bot_or_exists_ne_one.resolve_left hrne
    obtain ⟨y,hy,hxy⟩ := he ▸ mem_map_of_mem f hx
    have hxk : y⁻¹*x∈f.ker := f.eq_iff.mp hxy.symm
    have hyfix : (y:(A).Universal) • l.penultimate=l.penultimate := (pathRoot_fixes l hy).2
    have hxfix : (x:(A).Universal) • l.penultimate=l.penultimate := by
      have hh := halfPathLinearMap_kernel_fixes_neighbors h p 4 hlen e (y⁻¹*x) hxk _
        (l.adj_penultimate hlnil).symm
      have hh' := congrArg (fun z => (y:(A).Universal) • z) hh
      simpa only [coe_mul,coe_inv,mul_smul,smul_inv_smul,hyfix] using hh'
    have hh : (x:(A).Universal)∈pathRoot (X := (A).Universal) r ⊓
        MulAction.stabilizer (A).Universal l.penultimate := ⟨hx,hxfix⟩
    rw [pathRoot_inf_stabilizer_eq_bot r _ hoddq] at hh
    exact hxne (Subtype.ext hh)
  obtain ⟨P,hP⟩ := Matrix.SpecialLinearGroup.two_subgroup_image_is_sylow f R'
    (pathRoot_isTwo r).comap_subtype hcR hrk
  obtain ⟨Q,hQ⟩ := Matrix.SpecialLinearGroup.two_subgroup_image_is_sylow f U
    (pathRoot_isTwo l).comap_subtype hcU huk
  have hPQ : P≠Q := by
    intro hh
    exact hne (hP.symm.trans ((congrArg Sylow.toSubgroup hh).trans hQ))
  obtain ⟨z,hzP,hzQ⟩ := Matrix.SpecialLinearGroup.exists_opposite_sylow_marking 2 P Q hPQ
  rw [hP,hR,Subgroup.map_map] at hzP
  rw [hQ,Subgroup.map_map] at hzQ
  exact ⟨hR ▸ hrk,huk,z,hzP,hzQ⟩

/-- Both genuine roots embed in the same original quotient, with complete
upper/lower coordinates. Opposite reciprocal parameters give involutions
whose product has cube in the actor's own two-core. -/
theorem original_elementary_apartment_root_coordinates :
    ∃ m, 0 < m ∧ ∃ (K : Bool → Type) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Finite (K i)) (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i) = 2^(if i then m else 2*m)) ∧
    ∃ e : ∀ v : Vertex F,
      (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type),
    ∀ {a b} (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=8),
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c t)) →
      let D := halfPathActor (X := (A).Universal) p 4
      let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
      let U := (pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D
      let k := K ((bOne_tree_cover h).vertex (p.getVert 4)).type
      let f := halfPathLinearMap h p 4 hl (e ((bOne_tree_cover h).vertex (p.getVert 4)))
      Function.Surjective f ∧ f.ker=pCore 2 D ∧
        R ⊓ pCore 2 D=⊥ ∧ U ⊓ pCore 2 D=⊥ ∧
        ∃ z : SL(2,k),
          R.map ((MulAut.conj z).toMonoidHom.comp f)=Matrix.SpecialLinearGroup.upperUnipotent k ∧
          (∀ y : SL(2,k), y∈U.map ((MulAut.conj z).toMonoidHom.comp f) ↔
            ∃ a : k, Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero a=y) ∧
          ∀ x∈R, x≠1 → ∃ y∈U, x*x=1 ∧ y*y=1 ∧ (x*y)^3∈pCore 2 D := by
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hactors⟩ :=
    original_elementary_apartment_actor_quotients h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
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
  intro a b p hp hl hT D R U k f
  obtain ⟨hf,hker,_⟩ := hactors p hp hl hT
  obtain ⟨hr,hu,z,hzR,hzU⟩ := elementary_four_root_coordinates h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT (e _) (hval _)
  refine ⟨hf,hker,by simpa only [hker] using hr,by simpa only [hker] using hu,z,hzR,hzU,?_⟩
  let g := (MulAut.conj z).toMonoidHom.comp f
  have hgker : g.ker=pCore 2 D := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective]
    exact hker
  have hrg : R ⊓ g.ker=⊥ := by rw [hgker,←hker]; exact hr
  have hug : U ⊓ g.ker=⊥ := by rw [hgker,←hker]; exact hu
  intro x hx hne
  have him : g x∈Matrix.SpecialLinearGroup.upperUnipotent k :=
    hzR ▸ mem_map_of_mem g hx
  obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent k (g x)).mp him
  have hane : a≠0 := by
    intro he
    apply hne
    apply NaturalCubic.eq_one_of_root_kernel g R hrg x hx
    simpa only [he,Matrix.SpecialLinearGroup.transvection_coeff_zero] using ha.symm
  have hlow : NaturalCubic.lower a⁻¹∈U.map g := (hzU _).mpr ⟨_,rfl⟩
  obtain ⟨y,hy,hgy⟩ := hlow
  refine ⟨y,hy,NaturalCubic.square_of_image_upper g R hrg x hx a ha.symm,
    NaturalCubic.square_of_image_lower g U hug y hy a⁻¹ hgy,?_⟩
  rw [←hgker]
  change g ((x*y)^3)=1
  rw [map_pow,map_mul,←ha,hgy]
  exact NaturalCubic.cubic_cube a hane

omit c t htfix htmove htsq htnorm in
/-- The original nonbinary elementary source constructs the apartment,
quotient markings and both full root coordinates without catalogue,
reflection, root-injectivity or root-image premises. -/
theorem original_elementary_nonbinary_root_coordinates
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i = base T i) ∧
      (∀ i, t i • base T (!i) ≠ base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan (chosenCartans h) : Set (A).Universal)) ∧
    ∃ m, 0 < m ∧ ∃ (K : Bool → Type) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Finite (K i)) (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i) = 2^(if i then m else 2*m)) ∧
    ∃ e : ∀ v : Vertex F,
      (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type),
    ∀ {a b} (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=8),
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup (chosenCartans h) t)) →
      let D := halfPathActor (X := (A).Universal) p 4
      let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
      let U := (pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D
      let k := K ((bOne_tree_cover h).vertex (p.getVert 4)).type
      let f := halfPathLinearMap h p 4 hl (e ((bOne_tree_cover h).vertex (p.getVert 4)))
      Function.Surjective f ∧ f.ker=pCore 2 D ∧
        R ⊓ pCore 2 D=⊥ ∧ U ⊓ pCore 2 D=⊥ ∧
        ∃ z : SL(2,k),
          R.map ((MulAut.conj z).toMonoidHom.comp f)=Matrix.SpecialLinearGroup.upperUnipotent k ∧
          (∀ y : SL(2,k), y∈U.map ((MulAut.conj z).toMonoidHom.comp f) ↔
            ∃ a : k, Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero a=y) ∧
          ∀ x∈R, x≠1 → ∃ y∈U, x*x=1 ∧ y*y=1 ∧ (x*y)^3∈pCore 2 D := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb (chosenCartans h)
  exact ⟨t,htfix,htmove,htsq,htnorm,
    original_elementary_apartment_root_coordinates h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
