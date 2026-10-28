module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorFaithful
public import Theory.GroupTheory.InvolutiveSupplementNormalizer
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathMidpointCoordinates


/-!
# Reflections inside the faithful elementary apartment actors

A midpoint involution lies in the intrinsic Sylow-generated local group.
If it normalizes the prescribed Cartan, its commutator with the Cartan's
full local-kernel part lies both in that odd Cartan and in the midpoint
two-core. Thus it centralizes the kernel part, proving the corresponding
clause of DGS (14.2) without a nontriviality assumption.

Under the nontrivial Cartan-kernel condition of (14.5)(c), the proved faithful
two-root actor complements the midpoint core. A reflection reversing its
path normalizes the actor. Adjoining that involution contributes at most
two cosets, so any resulting kernel is fixed by the full Cartan. The source
Cartan-core centralizer theorem kills it. Consequently the reflection was
already in the two-root actor. Apartment edge coordinates construct such
a reflection at every supported eight-path, using the same chosen Cartan.

The final application retains the literal midpoint SL2 isomorphism, cubic
root pairs, original covering map and constructed reflection. The
Cartan-kernel nontriviality condition, exchange and root signs, binary
choices, nonelementary catalogue exclusions and full original (11.7)--(11.8)
marked assembly remain obligations of this family.
Source: DGS, Groups and Graphs (1985), (14.2)--(14.3), pp.210--212;
(14.5), p.213; (14.9), p.215; source profile (11.7), pp.174--175.
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

omit hp in
/-- Every involutive midpoint fixer normalizing the prescribed Cartan
centralizes its full local-kernel part. This clause of (14.2) requires no
nontriviality of that part. -/
theorem original_elementary_nonbinary_reflection_kernel
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (u : (A).Universal) (hu2 : u*u=1)
    (huC : u∈normalizer (cartan c : Set (A).Universal))
    (hufix : u • p.getVert 4=p.getVert 4) :
    ∀ k∈cartan c ⊓ (U F ((bOne_tree_cover h).vertex (p.getVert 4))).comap
      (bOne_tree_map h), Commute u k := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let v := cov.vertex (p.getVert 4)
  let w := cov.vertex (p.getVert 5)
  let J := graphLocalGroup F v
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hvw : (graph F).Adj v w := cov.hom.map_adj (p.adj_getVert_succ (by omega))
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,_⟩ :=
    original_elementary_apartment_actor_quotients h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  have hm2 : 2≤m := by
    by_contra hn
    have he : m=1 := by omega
    apply hnb
    let J₀ := graphLocalGroup F (base F true)
    let j := J₀.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
    refine ⟨K true,inferInstance,inferInstance,?_,?_⟩
    · simpa only [he,ite_true,Nat.pow_one] using hK true
    · exact ⟨(QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).symm.trans
        ((e (base F true)).trans
          (Atlas.RankOneFieldAutomorphisms.slEquivPSL : SL(2,K true) ≃* PSL(2,K true)))⟩
  have hfour : 4≤Nat.card (K v.type) := by
    rw [hK]
    apply (show 2^2≤2^(if v.type then m else 2*m) from
      Nat.pow_le_pow_right (by decide) ?_)
    cases v.type <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  have hJU : J ⊓ U F v=Q F v := CommutingTrivial.nonbinary_local_kernel_intersection
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw (e v) hfour
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite (Q F v) := Finite.of_injective (inclusion (Q_le_stabilizer F v))
    (inclusion_injective _)
  have hdis : Disjoint C (Q F v) := by
    have hpQ : IsPGroup 2 (Q F v) := isPGroup_pCoreIn 2 _
    obtain ⟨r,hr⟩ := hpQ.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have huv : φ u∈stabilizer F v := by
    change φ u • cov.vertex (p.getVert 4)=_
    rw [←cov.vertex_smul,hufix]
  have huJ : φ u∈J := by
    have hpow : φ u^(2^1)=1 := by rw [pow_one,pow_two,←map_mul,hu2,map_one]
    exact pGroup_le_sylowGenerated (stabilizer F v) (zpowers (φ u))
      (zpowers_le.mpr huv) (IsPGroup.of_card_dvd_pow (by
        rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hpow)) (mem_zpowers _)
  have hunC : φ u∈normalizer (C : Set G₀) :=
    (cartan c).le_normalizer_map φ (mem_map_of_mem φ huC)
  intro k hk
  have hkfix : k • p.getVert 4=p.getVert 4 :=
    reflectionApartment_fixed c t htnorm k hk.1 _ (hT _ (p.getVert_mem_support 4))
  have hkv : φ k∈stabilizer F v := by
    change φ k • cov.vertex (p.getVert 4)=_
    rw [←cov.vertex_smul,hkfix]
  have hkC : φ k∈C := mem_map_of_mem φ hk.1
  have hkU : φ k∈U F v := hk.2
  let z := φ u*φ k*(φ u)⁻¹*(φ k)⁻¹
  have hzC : z∈C := C.mul_mem ((mem_normalizer_iff.mp hunC _).mp hkC) (C.inv_mem hkC)
  have hzJ : z∈J := by
    have hh := (mem_normalizer_iff.mp (sylowGenerated_normalized _ hkv) _).mp (J.inv_mem huJ)
    have he : z=φ u*(φ k*(φ u)⁻¹*(φ k)⁻¹) := by dsimp [z]; group
    rw [he]
    exact J.mul_mem huJ hh
  have hzU : z∈U F v := (U F v).mul_mem
    ((mem_normalizer_iff.mp (stabilizer_le_normalizer_ballKernel F v 1 huv) _).mp hkU)
      ((U F v).inv_mem hkU)
  have hz1 : z=1 := disjoint_def.mp hdis hzC (hJU.le ⟨hzJ,hzU⟩)
  have hcommute : φ u*φ k=φ k*φ u :=
    mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hz1)
  have hfixuk : (u*k) • p.getVert 4=p.getVert 4 := by rw [mul_smul,hkfix,hufix]
  have hfixku : (k*u) • p.getVert 4=p.getVert 4 := by rw [mul_smul,hufix,hkfix]
  have he := (cov.stabilizerEquiv (p.getVert 4)).injective
    (a₁ := ⟨u*k,hfixuk⟩) (a₂ := ⟨k*u,hfixku⟩)
    (Subtype.ext (show φ (u*k)=φ (k*u) by simpa only [map_mul] using hcommute))
  exact congrArg Subtype.val he

/-- An actual Cartan-normalizing involution reversing the eight-path lies
in its two-root actor. Thus adjoining it adds no extra core or extension. -/
theorem original_elementary_nonbinary_reflection_mem_actor
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hne : (cartan c).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥)
    (u : (A).Universal) (hu2 : u*u=1)
    (huC : u∈normalizer (cartan c : Set (A).Universal))
    (hrev : ∀ j≤8, u • p.getVert j=p.getVert (8-j)) :
    u∈halfPathActor (X := (A).Universal) p 4 := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let D := halfPathActor (X := (A).Universal) p 4
  let M := D.map φ
  let v := cov.vertex (p.getVert 4)
  let w := cov.vertex (p.getVert 5)
  let J := graphLocalGroup F v
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hvw : (graph F).Adj v w := cov.hom.map_adj (p.adj_getVert_succ (by omega))
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hactors⟩ :=
    original_elementary_apartment_actor_quotients h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,hker,_,hcover,_⟩ := hactors p hp hl hT
  have hzero : pCore 2 D=⊥ := original_elementary_nonbinary_actor_core_eq_bot
    h hc hb hcomm helem c t htfix htmove htsq htnorm p hp hl hT hnb hne
  have hdis : Disjoint M (Q F v) := by
    apply disjoint_def.mpr
    rintro x ⟨y,hy,rfl⟩ hxQ
    let z : D := ⟨y,hy⟩
    have hzQ : halfPathLocalMap h p 4 hl z∈pCore 2 J := by
      obtain ⟨a,ha,he⟩ := (CommutingTrivial.graphLocalGroup_core (reduced_triple h) v).ge hxQ
      have he' : halfPathLocalMap h p 4 hl z=a := Subtype.ext he.symm
      exact he'.symm ▸ ha
    have hzK : z∈(halfPathLinearMap h p 4 hl (e v)).ker := by
      rw [halfPathLinearMap_kernel]
      exact hzQ
    have hz1 : z=1 := hzero.le (hker.le hzK)
    exact (congrArg (fun z : D => φ z.val) hz1).trans (map_one φ)
  have hCD : C ≤ normalizer (M : Set G₀) :=
    (map_mono (original_elementary_cartan_normalizes_actor c t htnorm p hT)).trans
      (D.le_normalizer_map φ)
  have hCP : C ⊓ J ≤ M := (original_elementary_local_cartan_le_actor
    h hc hb hcomm helem c t htfix htmove htsq htnorm p hp hl hT).1
  have hCE : C ≤ stabilizer F v ⊓ stabilizer F w := by
    rintro _ ⟨k,hk,rfl⟩
    constructor
    · change φ k • cov.vertex (p.getVert 4)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm k hk _
        (hT _ (p.getVert_mem_support 4))]
    · change φ k • cov.vertex (p.getVert 5)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm k hk _
        (hT _ (p.getVert_mem_support 5))]
  let E := F false ⊓ F true
  let W := (twoGroup L S).map φ
  have hmapE : (originalMiddle A).map φ=E := by
    rw [show originalMiddle A=T false ⊓ T true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact cov.map_inf
  have hC0 : C ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hW0 : W ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hWn : E ≤ normalizer (W : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hWcore : W ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hW0 hWn
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hd0 : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨r,hr⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hg0 : C ⊔ E.pCoreIn 2=E := by
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
    hbase hvw C (hEbase ▸ hC0) hCE ho (hEbase ▸ hd0) (hEbase ▸ hg0)
  have hfixed : Q F v ⊓ centralizer (C : Set G₀)=⊥ :=
    original_elementary_nonbinary_cartan_core_centralizer h hc hb hcomm helem hnb
      hvw C hCE ho hd hg
  have huv : u • p.getVert 4=p.getVert 4 := hrev 4 (by decide)
  have hφuv : φ u∈stabilizer F v := by
    change φ u • cov.vertex (p.getVert 4)=_
    rw [←cov.vertex_smul,huv]
  have hφu2 : φ u*φ u=1 := by rw [←map_mul,hu2,map_one]
  have hφuJ : φ u∈J := by
    have hpow : φ u^(2^1)=1 := by simpa only [pow_one,pow_two] using hφu2
    exact pGroup_le_sylowGenerated (stabilizer F v) (zpowers (φ u))
      (zpowers_le.mpr hφuv) (IsPGroup.of_card_dvd_pow (by
        rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hpow)) (mem_zpowers _)
  have hunD : u∈normalizer (D : Set (A).Universal) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (pathRoot (X := (A).Universal) (p.drop 4) ⊔ pathRoot (X := (A).Universal) (p.take 4)).map _=_
    rw [Subgroup.map_sup]
    obtain ⟨ha,hb⟩ := pathRoot_halves_reflection p 4 hl u hrev
    exact (congrArg₂ (fun R V : Subgroup (A).Universal => R ⊔ V) hb ha).trans
      (sup_comm _ _)
  have huM : φ u∈M := involution_mem_supplement_of_cartan_control M (Q F v) C J
    (halfPathActor_map_le_local h p 4 hl) hcover hdis
    ((sylowGenerated_le _).trans (stabilizer_normalizes_Q F v)) hCD
    ((hCE.trans inf_le_left).trans (stabilizer_normalizes_Q F v)) hCP hfixed (φ u) hφuJ
    (D.le_normalizer_map φ (mem_map_of_mem φ hunD))
    ((cartan c).le_normalizer_map φ (mem_map_of_mem φ huC)) hφu2
  obtain ⟨d,hd,hdu⟩ := huM
  have hdv := halfPathActor_le_midpoint_stabilizer hl hd
  have he := (cov.stabilizerEquiv (p.getVert 4)).injective
    (a₁ := ⟨d,hdv⟩) (a₂ := ⟨u,huv⟩) (Subtype.ext hdu)
  have hdu' : d=u := congrArg Subtype.val he
  exact hdu' ▸ hd


/-- The chosen apartment supplies a reversing involution in the actual
two-root actor, centralizing the full Cartan-kernel part. -/
theorem original_elementary_nonbinary_actor_reflection
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hne : (cartan c).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥) :
    ∃ u∈halfPathActor (X := (A).Universal) p 4,
      u∈reflectionGroup c t ∧ u∈normalizer (cartan c : Set (A).Universal) ∧
      u*u=1 ∧ (∀ j≤8, u • p.getVert j=p.getVert (8-j)) ∧
      ∀ k∈cartan c ⊓ (U F ((bOne_tree_cover h).vertex (p.getVert 4))).comap
        (bOne_tree_map h), Commute u k := by
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have hthick := original_source_tree_thickness h t
  let ρ := pathRoots h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  let N := reflectionGroup c t
  have ha := pathRoots_a h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  have hb' := pathRoots_b h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick
  have hlift := reflection_mem_apartmentGroup c ρ
  have hnorm := reflectionGroup_normalizes c t htnorm
  have hline := cartanApartment_noBranching A N (cartan c) ρ ha hb' hlift
    (cartan_le c) hnorm le_rfl htsq
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
  obtain ⟨g,hg,i,hgv,hgw⟩ := cartanApartment_edge_coordinates A N ρ ha hb' hlift hline
    (hT _ (p.getVert_mem_support 4)) (hT _ (p.getVert_mem_support 5))
    (p.adj_getVert_succ (by omega))
  let u := g*t i*g⁻¹
  have huu : u*u=1 := by
    calc
      _ = g*(t i*t i)*g⁻¹ := by dsimp [u]; group
      _ = 1 := by rw [htsq,mul_one,mul_inv_cancel]
  have huN : u∈N := N.mul_mem (N.mul_mem hg (reflectionGroup_mem c t i)) (N.inv_mem hg)
  have hufix : u • p.getVert 4=p.getVert 4 := by
    rw [←hgv]
    change (g*t i*g⁻¹) • (g • base T i)=g • base T i
    rw [mul_smul,mul_smul,inv_smul_smul,htfix]
  have humove : u • p.getVert 5≠p.getVert 5 := by
    rw [←hgw]
    change (g*t i*g⁻¹) • (g • base T (!i))≠g • base T (!i)
    rw [mul_smul,mul_smul,inv_smul_smul]
    exact fun he => htmove i ((MulAction.toPerm g).injective he)
  have hrev := reverses_path_of_moves_midpoint_neighbor (source_action A) hline p hp 4
    (by decide) hl hT u huu (fun _ hz => cartanApartment_preserves A N huN hz) hufix humove
  have huD := original_elementary_nonbinary_reflection_mem_actor h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT hnb hne u huu (hnorm huN) hrev
  refine ⟨u,huD,huN,hnorm huN,huu,hrev,?_⟩
  exact original_elementary_nonbinary_reflection_kernel h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hl hT hnb u huu (hnorm huN) hufix

omit c t htfix htmove htsq htnorm p hp hl hT in
/-- The original source supplies the apartment and its faithful actors,
including an actual reversing involution in each actor. Only the nontrivial
Cartan-kernel clause of (14.5)(c) remains at the supported path. -/
theorem original_elementary_nonbinary_reflected_apartment
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i=base T i) ∧
      (∀ i, t i • base T (!i)≠base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan (chosenCartans h) : Set (A).Universal)) ∧
    ∃ m, 0 < m ∧ ∃ (K : Bool → Type) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Finite (K i)) (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i) = 2^(if i then m else 2*m)) ∧
    ∃ e : ∀ v : Vertex F,
      (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type),
    ∀ {a b} (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=8),
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup (chosenCartans h) t)) →
      (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
        U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥ →
      let D := halfPathActor (X := (A).Universal) p 4
      let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
      let V := (pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D
      let k := K ((bOne_tree_cover h).vertex (p.getVert 4)).type
      pCore 2 D=⊥ ∧
      (∃ E : D ≃* SL(2,k),
        (∀ x, E x=e _ (QuotientGroup.mk' _ (halfPathLocalMap h p 4 hl x))) ∧
        ∀ x∈R, x≠1 → ∃ y∈V, x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3) ∧
      ∃ u∈D, u∈reflectionGroup (chosenCartans h) t ∧
        u∈normalizer (cartan (chosenCartans h) : Set (A).Universal) ∧
        u*u=1 ∧ (∀ j≤8, u • p.getVert j=p.getVert (8-j)) ∧
        ∀ k∈cartan (chosenCartans h) ⊓
          (U F ((bOne_tree_cover h).vertex (p.getVert 4))).comap (bOne_tree_map h),
          Commute u k := by
  obtain ⟨t,htfix,htmove,htsq,htnorm,m,hm,K,fK,finK,chK,hK,e,hactors⟩ :=
    original_elementary_nonbinary_faithful_apartment h hc hb hcomm helem hnb
  let _ := fK
  let _ := finK
  let _ := chK
  refine ⟨t,htfix,htmove,htsq,htnorm,m,hm,K,fK,finK,chK,hK,e,?_⟩
  intro a b p hp hl hT hne D R V k
  obtain ⟨hzero,E,hmap,hpairs⟩ := hactors p hp hl hT hne
  exact ⟨hzero,⟨E,hmap,hpairs⟩,original_elementary_nonbinary_actor_reflection
    h hc hb hcomm helem (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT hnb hne⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
