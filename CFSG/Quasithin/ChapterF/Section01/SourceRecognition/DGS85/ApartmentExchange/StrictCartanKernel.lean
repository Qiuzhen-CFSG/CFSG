module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorMarkedCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanDistinctSource
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootCartanTransitivity

/-!
# The full strict Cartan has a nontrivial local permutation kernel

The two disjoint local tori give a product lower bound for the order of the
same full chosen Cartan. If its midpoint permutation kernel were trivial,
conjugation on a nonidentity element of a literal half-path root would be
injective: the Cartan is abelian and transitive on the nonidentity root
elements, and a root centralizer fixes the whole midpoint neighborhood.
The root has order q, smaller than the product of the two nonbinary torus
orders. All fields, tori, root coordinates, and path geometry come from
the unchanged original strict source inputs.

Source: DGS, Groups and Graphs (1985), (10.7)--(10.10), pp.158--165,
and (14.3), (14.5), (14.9), pp.212--216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment

private theorem abelian_conjugation_card_le
    {X : Type*} [Group X] (C R : Subgroup X) [IsMulCommutative C] [Finite R]
    (hn : C≤normalizer (R : Set X)) (hne : R≠⊥)
    (htrans : ∀ x∈R, ∀ y∈R, x≠1 → y≠1 → ∃ c∈C, c*x*c⁻¹=y)
    (hfaith : ∀ c∈C, (∀ x∈R, Commute c x) → c=1) :
    Nat.card C≤Nat.card R := by
  obtain ⟨r,hr,hr1⟩ := R.bot_or_exists_ne_one.resolve_left hne
  let j : C → R := fun c => ⟨c*r*(c:X)⁻¹,(mem_normalizer_iff.mp (hn c.property) r).mp hr⟩
  apply Nat.card_le_card_of_injective j
  intro x y he
  let d : X := (y:X)⁻¹*x
  have hd : d∈C := C.mul_mem (C.inv_mem y.property) x.property
  have hdr : Commute d r := by
    have hh := congrArg (fun z : R => (y:X)⁻¹*(z:X)*(x:X)) he
    change (y:X)⁻¹*((x:X)*r*(x:X)⁻¹)*(x:X)=
      (y:X)⁻¹*((y:X)*r*(y:X)⁻¹)*(x:X) at hh
    change d*r=r*d
    dsimp only [d]
    convert hh using 1 <;> group
  have hd1 : d=1 := hfaith d hd (by
    intro s hs
    by_cases hs1 : s=1
    · rw [hs1]; exact Commute.one_right _
    obtain ⟨c,hc,heq⟩ := htrans r hr s hs hr1 hs1
    have hcd : Commute c d := setLike_mul_comm hc hd
    have hh := hdr.conj c
    simpa only [hcd.mul_inv_cancel,heq] using hh)
  exact Subtype.ext (inv_mul_eq_one.mp hd1).symm

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S

private theorem chosen_cartan_product_bound
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false),Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj (base F true) u)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ v : Vertex F, (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type)) :
    (Nat.card (K false)-1)*(Nat.card (K true)-1)≤Nat.card (cartan (chosenCartans h)) := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let c := chosenCartans h
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let _ : Finite (cartan c) := Nat.finite_of_card_ne_zero (by
    intro hz
    have hh := cartan_odd c
    rw [hz] at hh
    norm_num at hh)
  let _ : Finite C := Finite.of_surjective (φ.subgroupMap (cartan c))
    (φ.subgroupMap_surjective (cartan c))
  let E := F false ⊓ F true
  let W := (twoGroup L S).map φ
  have hmapE : (originalMiddle A).map φ=E := by
    rw [show originalMiddle A=T false ⊓ T true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact cov.map_inf
  have hCE : C≤E := hmapE ▸ map_mono (cartan_le c)
  have hWE : W≤E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hnW : E≤normalizer (W : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hWcore : W≤E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hWE hnW
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite E := Finite.of_injective (inclusion (show E≤F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hd : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨r,hr⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hg : C ⊔ E.pCoreIn 2=E := by
    apply le_antisymm (sup_le hCE (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    exact he.symm.le.trans (sup_le (hWcore.trans le_sup_right) le_sup_left)
  have hEbase : E=stabilizer F (base F false) ⊓ stabilizer F (base F true) := by
    rw [show stabilizer F (base F false)=F false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F (base F true)=F true from Subgroup.CosetGeometry.stabilizer_base _ _]
  have hab : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨⟨eα⟩,_⟩ := CommutingTrivial.edge_complement_local_torus H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hab (e (base F false)) C
    (hEbase ▸ hCE) (hEbase ▸ hd) (hEbase ▸ hg)
  obtain ⟨⟨eβ⟩,_⟩ := CommutingTrivial.edge_complement_local_torus H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hab.symm (e (base F true)) C
    (by rw [inf_comm]; exact hEbase ▸ hCE)
    (by rw [inf_comm]; exact hEbase ▸ hd)
    (by
      change C ⊔ (stabilizer F (base F true) ⊓ stabilizer F (base F false)).pCoreIn 2 =
        stabilizer F (base F true) ⊓ stabilizer F (base F false)
      rw [inf_comm (stabilizer F (base F true)) (stabilizer F (base F false))]
      exact hEbase ▸ hg)
  have hca : Nat.card (C ⊓ graphLocalGroup F (base F false) : Subgroup G₀)=Nat.card (K false)-1 :=
    (Nat.card_congr eα.toEquiv).trans (Nat.card_units (α := K false))
  have hcb : Nat.card (C ⊓ graphLocalGroup F (base F true) : Subgroup G₀)=Nat.card (K true)-1 :=
    (Nat.card_congr eβ.toEquiv).trans (Nat.card_units (α := K true))
  obtain ⟨k,f,fin,ch,alg,d,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have hsep := bTwo_odd_local_tori_disjoint H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) d hactor (reduced_bTwo_middle_central h hc hne hb hab hβu)
    (base_Z_ne_bot H true) C ho
  let _ : IsMulCommutative (cartan c) := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hcomm : C ⊓ graphLocalGroup F (base F false)≤
      centralizer (C ⊓ graphLocalGroup F (base F true) : Set G₀) := by
    intro x hx
    exact mem_centralizer_iff.mpr (fun y hy => setLike_mul_comm hy.1 hx.1)
  obtain ⟨ep,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (C ⊓ graphLocalGroup F (base F false)) (C ⊓ graphLocalGroup F (base F true)) hsep hcomm
  have hprod : Nat.card ((C ⊓ graphLocalGroup F (base F false)) ⊔
      (C ⊓ graphLocalGroup F (base F true)) : Subgroup G₀)=
        (Nat.card (K false)-1)*(Nat.card (K true)-1) := by
    rw [←Nat.card_congr ep.toEquiv,Nat.card_prod,hca,hcb]
  have hbound : (Nat.card (K false)-1)*(Nat.card (K true)-1)≤Nat.card C := by
    rw [←hprod]
    exact Nat.le_of_dvd Nat.card_pos (card_dvd_of_le (sup_le inf_le_left inf_le_left))
  exact hbound.trans (Nat.le_of_dvd Nat.card_pos ((cartan c).card_map_dvd φ))

private theorem right_root_centralizer_le_kernel
    (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection))
    (k : (A).Universal) (hk : k∈cartan c)
    (hc : ∀ x∈pathRoot (X := (A).Universal) (p.drop 6), Commute k x) :
    bOne_tree_map h k∈U F ((bOne_tree_cover h).vertex (p.getVert 6)) := by
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
  have hTr : ∀ z∈r.support, z∈cartanApartment A (reflectionGroup c d.reflection) := by
    intro z hz
    simp only [r,support_reverse,List.mem_reverse] at hz
    rw [drop_support_eq_support_drop_min] at hz
    exact hT z (List.mem_of_mem_drop hz)
  have hfix (j : ℕ) : k • p.getVert j=p.getVert j :=
    reflectionApartment_fixed c d.reflection d.normalizes k hk _ (hT _ (p.getVert_mem_support j))
  have hK : cartan c≤pathFixer (X := (A).Universal) r := by
    intro x hx j _
    exact reflectionApartment_fixed c d.reflection d.normalizes x hx _ (hTr _ (r.getVert_mem_support j))
  have hnewl : l.penultimate∉r.support := by
    intro hm
    exact hdiff (htree.eq_penultimate_of_adj_end (hp.drop 6).reverse (l.adj_penultimate hlnil).symm hm)
  have hodd := d.odd (r.concat (l.adj_penultimate hlnil).symm)
    ((hp.drop 6).reverse.concat hnewl _) (by rw [length_concat,hrl])
  have hfactor := apartment_path_factorization h c 6 (by decide) d.reflection d.fixes d.moves
    d.squares d.normalizes d.transitive d.thick r (by omega) hTr
  have hKc : ∀ x∈cartan c, x • l.penultimate=l.penultimate := by
    intro x hx
    rw [hprevl]
    exact reflectionApartment_fixed c d.reflection d.normalizes x hx _
      (hT _ (p.getVert_mem_support 5))
  have hstar := (pathRoot_commute_iff_fixes_neighbors htree (source_action A)
    r (hp.drop 6).reverse (by rw [hrl]; exact d.transitive) (cartan c) hK
    (l.adj_penultimate hlnil).symm hdiff hKc hfactor hodd k hk).mp (by
        simpa only [r,pathRoot_reverse] using hc)
  intro w hw
  rcases (Subgroup.CosetGeometry.RankTwo.mem_ball_one F _ w).mp hw with hw | rfl
  · obtain ⟨z,hz⟩ := ((bOne_tree_cover h).neighbor_bijective (p.getVert 6)).2 ⟨w,hw⟩
    have he : (bOne_tree_cover h).vertex z.val=w := congrArg Subtype.val hz
    rw [←he,←(bOne_tree_cover h).vertex_smul,hstar z.val z.property]
  · rw [←(bOne_tree_cover h).vertex_smul,hfix 6]

variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆≠⊥)
  (hb : b (reducedFamily L S)=2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

/-- The same full original Cartan has nontrivial intersection with the whole
midpoint permutation kernel on every actual strict-source twelve-path. -/
theorem strict_source_cartan_kernel_ne_bot
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear) :
    (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6))≠⊥ := by
  obtain ⟨K,fK,finK,chK,hK,e,hmarks⟩ :=
    strict_source_small_actor_marked_coordinates h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,_,hRker,_,z,hR,_,hfull⟩ := hmarks p hp hl hT
  let D := halfPathActor (X := (A).Universal) p 6
  let R₀ := pathRoot (X := (A).Universal) (p.drop 6)
  let R := R₀.subgroupOf D
  let c := chosenCartans h
  let C := cartan c
  let C' := C.subgroupOf D
  let v := (bOne_tree_cover h).vertex (p.getVert 6)
  let k := K v.type
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl (e v))
  let d := strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear
  let _ : IsMulCommutative C := cartan_abelian h c
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : Finite (graphLocalGroup F v) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 6 hl)
  have hRk : R ⊓ f.ker=⊥ := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective]
    exact hRker
  have hfix (x) (hx : x∈C) (j : ℕ) : x • p.getVert j=p.getVert j :=
    reflectionApartment_fixed c d.reflection d.normalizes x hx _ (hT _ (p.getVert_mem_support j))
  have hn : C≤normalizer (R₀ : Set (A).Universal) := by
    intro x hx
    apply pathFixer_le_normalizer_pathRoot (p.drop 6)
    intro j _
    rw [drop_getVert]
    exact hfix x hx _
  have hn' : C'≤normalizer (R : Set D) := by
    intro x hx
    exact mem_normalizer_iff.mpr (fun y => mem_normalizer_iff.mp (hn hx) y.val)
  let rmap : R →* Matrix.SpecialLinearGroup.upperUnipotent k :=
    (f.comp R.subtype).codRestrict _ (fun x => hR ▸ mem_map_of_mem f x.property)
  have hrinj : Function.Injective rmap := by
    intro x y he
    apply Subtype.ext
    apply inv_mul_eq_one.mp
    apply hRk.le
    refine ⟨R.mul_mem (R.inv_mem x.property) y.property,?_⟩
    change f ((x:D)⁻¹*y)=1
    rw [map_mul,map_inv,show f x=f y from congrArg Subtype.val he,inv_mul_cancel]
  have hron : Function.Surjective rmap := by
    intro y
    have hym : (y:SL(2,k))∈R.map f := hR.symm ▸ y.property
    obtain ⟨x,hx,he⟩ := hym
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hcardR : Nat.card R₀=Nat.card k := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe (show R₀≤D from le_sup_left)).toEquiv]
    exact (Nat.card_congr (MulEquiv.ofBijective rmap ⟨hrinj,hron⟩).toEquiv).trans
      (Matrix.SpecialLinearGroup.card_upperUnipotent k)
  let _ : Finite R₀ := Nat.finite_of_card_ne_zero (by rw [hcardR]; exact Nat.card_pos.ne')
  have hRne : R₀≠⊥ := by
    intro he
    have hh := hK v.type
    rw [he,card_bot] at hcardR
    change 4≤Nat.card k at hh
    omega
  have htrans : ∀ x∈R₀, ∀ y∈R₀, x≠1 → y≠1 → ∃ a∈C, a*x*a⁻¹=y := by
    intro x hx y hy hx1 hy1
    let x' : D := ⟨x,(show R₀≤D from le_sup_left) hx⟩
    let y' : D := ⟨y,(show R₀≤D from le_sup_left) hy⟩
    obtain ⟨a,ha,he⟩ := NaturalCubic.upper_root_cartan_transitive f R C' hRk hn' hR hfull
      x' y' hx hy (fun he => hx1 (congrArg Subtype.val he))
      (fun he => hy1 (congrArg Subtype.val he))
    exact ⟨a,ha,congrArg Subtype.val he⟩
  intro hzero
  have hbound : Nat.card C≤Nat.card k := by
    rw [←hcardR]
    apply abelian_conjugation_card_le C R₀ hn hRne htrans
    intro x hx hxc
    have hxU := right_root_centralizer_le_kernel h c d p hp hl hT x hx hxc
    have hx1 : bOne_tree_map h x=1 :=
      hzero.le ⟨mem_map_of_mem (bOne_tree_map h) hx,hxU⟩
    have he := (bOne_tree_cover h).stabilizerEquiv (p.getVert 6) |>.injective
      (a₁ := ⟨x,hfix x hx 6⟩) (a₂ := 1) (Subtype.ext (hx1.trans (map_one _).symm))
    exact congrArg Subtype.val he
  have hprod := chosen_cartan_product_bound h hc hne hb hβu K e
  have h0 := hK false
  have h1 := hK true
  change Nat.card C≤Nat.card (K v.type) at hbound
  have hboth : (Nat.card (K false)-1)*(Nat.card (K true)-1)≤Nat.card (K v.type) :=
    hprod.trans hbound
  have hp0 : 3≤Nat.card (K false)-1 := by omega
  have hp1 : 3≤Nat.card (K true)-1 := by omega
  have he0 : Nat.card (K false)-1+1=Nat.card (K false) := Nat.sub_add_cancel (by omega)
  have he1 : Nat.card (K true)-1+1=Nat.card (K true) := Nat.sub_add_cancel (by omega)
  cases hv : v.type <;> rw [hv] at hboth
  · nlinarith only [hboth,hp0,hp1,he0]
  · nlinarith only [hboth,hp0,hp1,he1]

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
