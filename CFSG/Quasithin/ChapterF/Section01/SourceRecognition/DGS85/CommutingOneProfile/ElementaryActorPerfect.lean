module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryRootCoordinates
public import Theory.SpecificGroups.SL2.RootLiftDerived

/-!
# Perfectness of the actual nonbinary elementary two-root actor

The same full apartment Cartan complements the two-core of every supported
edge. Its intersection with the intrinsic midpoint group is the full local
torus and lies inside the two-root actor. Its image is nontrivial and odd
when the beta field is nonbinary. It normalizes both actual four-path roots.
The rank-one commutator calculation therefore puts both roots in the
actor's derived subgroup, so their join is perfect.

This uses the literal original covering map and the two simultaneous root
markings. It requires neither the nontrivial Cartan-kernel clause of (14.5)(c)
nor an assumed perfect extension. ElementaryActorFaithful combines it with
the proved derived-core separation to eliminate the entire actor core.
Source: DGS, Groups and Graphs (1985), (14.3), p.212, and the nonbinary
r=4 argument in (14.9), p.215; source profile (11.7), pp.174--175.
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

/-- The actual nonbinary elementary two-root actor is perfect. -/
theorem original_elementary_nonbinary_actor_perfect
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    Group.IsPerfect (halfPathActor (X := (A).Universal) p 4) := by
  let D := halfPathActor (X := (A).Universal) p 4
  let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
  let V := (pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 4)
  let w := cov.vertex (p.getVert 5)
  let J := graphLocalGroup F v
  let C₀ := (cartan c).map φ
  let C := (cartan c ⊓ J.comap φ).subgroupOf D
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 4 hl)
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hroots⟩ :=
    original_elementary_apartment_root_coordinates h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  let k := K v.type
  obtain ⟨hf,hker,hr,hv,z,hR,hV,hxy⟩ := hroots p hp hl hT
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 4 hl (e v))
  have hfk : f.ker=pCore 2 D :=
    (MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective).trans hker
  have hRk : R ⊓ f.ker=⊥ := by rw [hfk]; exact hr
  have hVk : V ⊓ f.ker=⊥ := by rw [hfk]; exact hv
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
  have hfour : 4≤Nat.card k := by
    change 4≤Nat.card (K v.type)
    rw [hK]
    apply (show 2^2≤2^(if v.type then m else 2*m) from
      Nat.pow_le_pow_right (by decide) ?_)
    cases v.type <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  have hCD : cartan c ⊓ J.comap φ ≤ D :=
    (original_elementary_local_cartan_le_actor h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT).2
  have hCm : C.map (φ.comp D.subtype)=C₀ ⊓ J := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨mem_map_of_mem φ hy.1,hy.2⟩
    · rintro ⟨⟨y,hy,rfl⟩,hyJ⟩
      exact ⟨⟨y,hCD ⟨hy,hyJ⟩⟩,⟨hy,hyJ⟩,rfl⟩
  have hoC : Odd (Nat.card C) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCD).toEquiv]
    exact (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
      (card_dvd_of_le (show cartan c ⊓ J.comap φ ≤ cartan c from inf_le_left))
  have hCk : Disjoint C (pCore 2 D) := by
    obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact hoC.coprime_two_right.pow_right r)
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
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw (e v) C₀ hCE hd hg
  have hCne : C.map f≠⊥ := by
    intro hz
    have hCb : C=⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact disjoint_def.mp hCk hx (hfk ▸ (show x∈f.ker from
        (Subgroup.map_eq_bot_iff C).mp hz hx))
    have hCJ : C₀ ⊓ J=⊥ := by rw [←hCm,hCb,Subgroup.map_bot]
    have he := Nat.card_congr etor.toEquiv
    change Nat.card (C₀ ⊓ J : Subgroup G₀)=Nat.card kˣ at he
    rw [hCJ,card_bot,Nat.card_units] at he
    omega
  have hCn (q : (sourceGraph A).Walk a (p.getVert 4))
      (hqT : ∀ x∈q.support, x∈cartanApartment A (reflectionGroup c t)) :
      C ≤ normalizer ((pathRoot (X := (A).Universal) q).subgroupOf D : Set D) := by
    intro x hx
    have hfix : x.val∈pathFixer (X := (A).Universal) q := by
      intro j _
      exact reflectionApartment_fixed c t htnorm x.val hx.1 _ (hqT _ (q.getVert_mem_support j))
    have hn := pathFixer_le_normalizer_pathRoot q hfix
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp hn y.val
  have hCR : C ≤ normalizer (R : Set D) := by
    intro x hx
    have hfix : x.val∈pathFixer (X := (A).Universal) (p.drop 4) := by
      intro j _
      rw [drop_getVert]
      exact reflectionApartment_fixed c t htnorm x.val hx.1 _ (hT _ (p.getVert_mem_support _))
    have hn := pathFixer_le_normalizer_pathRoot (p.drop 4) hfix
    exact mem_normalizer_iff.mpr (fun y => mem_normalizer_iff.mp hn y.val)
  have hCV : C ≤ normalizer (V : Set D) := by
    apply hCn (p.take 4)
    intro x hx
    rw [support_take] at hx
    exact hT x (List.mem_of_mem_take hx)
  have hoim : Odd (Nat.card (C.map f)) := hoC.of_dvd_nat (C.card_map_dvd f)
  have hRd : R ≤ _root_.commutator D := Matrix.SpecialLinearGroup.sylow_lift_le_commutator
    f R C (Matrix.SpecialLinearGroup.upperUnipotentSylow k 2) hR hRk hCR hoim hCne
  have hVcard : Nat.card (V.map f)=Nat.card k := by
    let j : k → V.map f := fun a => ⟨NaturalCubic.lower a,(hV _).mpr ⟨a,rfl⟩⟩
    have hj : Function.Bijective j := by
      constructor
      · intro x y he
        have he' := congrArg (fun z : V.map f => z.val.val 1 0) he
        simpa [j,NaturalCubic.lower,Matrix.SpecialLinearGroup.transvection_coe] using he'
      · intro x
        obtain ⟨a,ha⟩ := (hV x.val).mp x.property
        exact ⟨a,Subtype.ext ha⟩
    exact (Nat.card_congr (Equiv.ofBijective j hj)).symm
  obtain ⟨Q,hQ⟩ := ((pathRoot_isTwo (X := (A).Universal) (p.take 4)).comap_subtype.map f).exists_le_sylow
  have hQeq : V.map f=(Q : Subgroup SL(2,k)) := by
    apply eq_of_le_of_card_ge hQ
    change Nat.card Q ≤ Nat.card (V.map f)
    rw [hVcard,←Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 Q).toEquiv]
    rfl
  have hVd : V ≤ _root_.commutator D := Matrix.SpecialLinearGroup.sylow_lift_le_commutator
    f V C Q hQeq hVk hCV hoim hCne
  have hgen : R ⊔ V=⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show pathRoot (X := (A).Universal) (p.drop 4) ≤ D from le_sup_left),
      map_subgroupOf_eq_of_le (show pathRoot (X := (A).Universal) (p.take 4) ≤ D from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  exact ⟨top_unique (hgen ▸ sup_le hRd hVd)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
