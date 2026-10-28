module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BinaryRootConjugacy
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorCentralCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryCartanKernels

/-!
# The elementary beta two-root actor, including the binary endpoint

At a binary beta--alpha edge the full Cartan has trivial intersection with
alpha's full local permutation kernel. Transport this fact along the original
reduced graph. The Cartan centralizer argument places the beta actor's own
two-core in every neighboring two-core, hence in the second ball kernel.
The established second-kernel formula then puts its image in the literal
Z_beta and makes it central elementary. An injectively lifted abelian Sylow
removes this core from the actor's derived subgroup by central transfer.

The binary source valence and the original center formula give |Z_beta| = 2.
Thus the actual beta actor core has order at most two. Reciprocal opposite
four-path roots have product of order three or six; its cube is central.
The last theorem constructs the same full-Cartan apartment from F.1.1 and
applies these conclusions to every supported beta eight-path, retaining the
universal-to-reduced map and the two literal half-path radicals.

These are the beta central-kernel steps toward binary exchange. The source
conjugacy-class separation in (14.8), elimination of the remaining central
correction, alpha complement argument, and complete marked quotient assembly
remain to be proved. No strict (14.9)(c) natural-actor input is used here.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.7), pp.174--175; (14.5)--(14.6), pp.213--214; (14.8)--(14.9),
pp.214--216; and the exchange argument (14.15), pp.219--220.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
open CommutingOneProfile CommutingTrivial
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
private theorem order_three_or_six {n : ℕ} (h3 : 3∣n) (h6 : n∣6) : n=3 ∨ n=6 := by
  have hn : n≤6 := Nat.le_of_dvd (by decide) h6
  interval_cases n <;> norm_num at *

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


omit c t htfix htmove htsq htnorm p hp hl hT in
/-- Transport the binary alpha Cartan-kernel equality to the actual edge. -/
theorem elementary_binary_alpha_cartan_kernel_at_edge
    (hbinary : ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    {v w : Vertex F} (hvw : (graph F).Adj v w) (hv : v.type=true)
    (C : Subgroup G₀) (hCE : C ≤ stabilizer F v ⊓ stabilizer F w)
    (ho : Odd (Nat.card C)) : C ⊓ U F w=⊥ := by
  have hw : w.type=false := by
    have hh := hvw.1
    change v.type≠w.type at hh
    cases he : w.type
    · rfl
    · exact (hh (hv.trans he.symm)).elim
  obtain ⟨g,hgw,hgv⟩ := incident_common_translate F hvw.symm.2
  rw [hw] at hgw
  rw [hv] at hgv
  let C' := C.map (MulAut.conj g⁻¹).toMonoidHom
  have hC'E : C' ≤ stabilizer F (base F false) ⊓ stabilizer F (base F true) := by
    rintro _ ⟨x,hx,rfl⟩
    constructor
    · change (g⁻¹*x*(g⁻¹)⁻¹) • base F false=base F false
      rw [inv_inv,mul_smul,mul_smul,hgw,(hCE hx).2,←hgw,inv_smul_smul]
    · change (g⁻¹*x*(g⁻¹)⁻¹) • base F true=base F true
      rw [inv_inv,mul_smul,mul_smul,hgv,(hCE hx).1,←hgv,inv_smul_smul]
  have ho' : Odd (Nat.card C') := by
    dsimp only [C']
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact ho
  have hz := original_elementary_binary_alpha_cartan_kernel_eq_bot
    h hc hb hcomm helem hbinary C' hC'E ho'
  apply bot_unique
  intro x hx
  have hxC : g⁻¹*x*g∈C' := by
    have hh := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx.1
    change g⁻¹*x*(g⁻¹)⁻¹∈C' at hh
    simpa only [inv_inv] using hh
  have hxU : x∈(U F (base F false)).map (MulAut.conj g).toMonoidHom := by
    have hh := hx.2
    change x∈ballKernel F w 1 at hh
    rw [←hgw,ballKernel_translate] at hh
    exact hh
  obtain ⟨y,hy,hyx⟩ := hxU
  have he : g⁻¹*x*g=y := by
    rw [←hyx]
    change g⁻¹*(g*y*g⁻¹)*g=y
    group
  have hx1 : g⁻¹*x*g=1 := hz.le ⟨hxC,he.symm ▸ hy⟩
  have hcancel : x=g*(g⁻¹*x*g)*g⁻¹ := by group
  rw [hcancel,hx1,mul_one,mul_inv_cancel]
  exact one_mem _

/-- The binary beta two-root core fixes the actual second ball. -/
theorem elementary_binary_beta_actor_core_radius_two
    (hbinary : ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type=true) :
    ((halfPathActor (X := (A).Universal) p 4).pCoreIn 2).map (bOne_tree_map h) ≤
      ballKernel F ((bOne_tree_cover h).vertex (p.getVert 4)) 2 ∧
    (halfPathActor (X := (A).Universal) p 4).pCoreIn 2 ≤
      ballKernel T (p.getVert 4) 2 := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let D := halfPathActor (X := (A).Universal) p 4
  let M := D.map φ
  let V := (D.pCoreIn 2).map φ
  let v := cov.vertex (p.getVert 4)
  let w := cov.vertex (p.getVert 5)
  have hvw : (graph F).Adj v w := cov.hom.map_adj (p.adj_getVert_succ (by omega))
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hactors⟩ :=
    original_elementary_apartment_actor_quotients h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  have hne := original_elementary_beta_cartan_kernel_ne_bot h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT hv
  obtain ⟨_,hker,_,hcover,_⟩ := hactors p hp hl hT
  have hVQ : V ≤ Q F v := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    have hxk := hker.symm ▸ hx
    rw [halfPathLinearMap_kernel] at hxk
    exact (CommutingTrivial.graphLocalGroup_core (reduced_triple h) v).le
      ⟨halfPathLocalMap h p 4 hl x,hxk,rfl⟩
  have hCN : cartan c ≤ normalizer (D.pCoreIn 2 : Set (A).Universal) :=
    (original_elementary_cartan_normalizes_actor c t htnorm p hT).trans
      (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
  have hCV : C ≤ normalizer (V : Set G₀) :=
    (map_mono hCN).trans ((D.pCoreIn 2).le_normalizer_map φ)
  have hMV : M ≤ normalizer (V : Set G₀) :=
    (map_mono (D.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))).trans
        ((D.pCoreIn 2).le_normalizer_map φ)
  have hcentral : C ⊓ U F v ≤ centralizer (M : Set G₀) := by
    rintro _ ⟨⟨k,hk,rfl⟩,hkU⟩
    have hkC : k∈centralizer (D : Set (A).Universal) :=
      ((original_elementary_cartan_actor_centralizer h hc hb hcomm helem
        c t htfix htmove htsq htnorm p hp hl hT).ge ⟨hk,hkU⟩).2
    apply mem_centralizer_iff.mpr
    rintro _ ⟨d,hd,rfl⟩
    exact (show Commute d k from mem_centralizer_iff.mp hkC d hd).map φ
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
  obtain ⟨_,_,_,_,_,_,_,_,_,hpar,_⟩ :=
    original_borel_elementary_orders_and_paths_of_source h hc hb hcomm helem
  have hs : sourceS (P := fun i => (P₀ L S i).subgroupOf G₀)=5 :=
    (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2.unique hpar.2
  have htrans := sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) v
    (show 1<sourceS (P := fun i => (P₀ L S i).subgroupOf G₀) by omega)
  have hCUw := elementary_binary_alpha_cartan_kernel_at_edge h hc hb hcomm helem
    hbinary hvw hv C hCE ho
  obtain ⟨r,hwr,hrv,hCr⟩ := edge_cartan_second_fixed_neighbor (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw htrans C hCE hd hg
  have hdis : Disjoint (C ⊓ U F v) (U F w) := by
    apply disjoint_def.mpr
    intro x hx hy
    exact hCUw.le ⟨hx.1,hy⟩
  have hVW : V ≤ Q F w := cartan_normalized_centralizing_two_subgroup_le_core
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    hvw.symm hwr hrv (e w) C V (C ⊓ U F v)
    (hCE.trans (inf_comm _ _).le) (by rw [inf_comm (stabilizer F w) (stabilizer F v)]; exact hd)
    (by rw [inf_comm (stabilizer F w) (stabilizer F v)]; exact hg)
    (le_inf (hVQ.trans ((source_Z_Q_U (reduced_triple h) v).2.trans
      ((ballKernel_one_le_edge F hvw).trans inf_le_right)))
      (hVQ.trans (Q_le_stabilizer F v)))
    ((isPGroup_pCoreIn 2 _).to_le hVQ) hCV inf_le_left
    (inf_le_left.trans hCr)
    (hcentral.trans (centralizer_le (map_mono (pCoreIn_le 2 D)))) hne hdis
  have hMN : M ≤ normalizer (Q F v : Set G₀) :=
    (halfPathActor_map_le_local h p 4 hl).trans
      ((sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Q F v))
  have hall : V ≤ neighborCoreIntersection F v := by
    apply le_iInf
    intro z
    obtain ⟨g,hgM,hgz⟩ : ∃ g∈M, g • w=z.val := by
      obtain ⟨g,hg',hgz⟩ := graphLocalGroup_transitive (reduced_triple h)
        (reduced_borel_core_sylow h) (reduced_vertex_sylow h) v ⟨w,hvw⟩ z
      have hprod : g∈(M : Set G₀)*(Q F v : Set G₀) := by
        rw [←coe_mul_of_left_le_normalizer_right M (Q F v) hMN,hcover]
        exact hg'
      obtain ⟨d,hd',q,hq,rfl⟩ := hprod
      refine ⟨d,hd',?_⟩
      have hqw : q • w=w := (source_Z_Q_U (reduced_triple h) v).2 hq w
        ((mem_ball_one F v w).mpr (Or.inl hvw))
      simpa only [mul_smul,hqw] using hgz
    intro x hx
    have hconj : g⁻¹*x*g∈V := by
      have hh := (mem_normalizer_iff.mp (hMV (M.inv_mem hgM)) x).mp hx
      simpa only [inv_inv] using hh
    rw [←hgz,Q_translate]
    refine ⟨g⁻¹*x*g,hVW hconj,?_⟩
    change g*(g⁻¹*x*g)*g⁻¹=x
    group
  have hVball : V ≤ ballKernel F v 2 :=
    hall.trans (source_neighborCoreIntersection_le_second_kernel (reduced_triple h) hvw.symm)
  refine ⟨hVball,?_⟩
  intro x hx
  exact cov.ballKernel_lift (p.getVert 4) 2 x
    (halfPathActor_le_midpoint_stabilizer hl (pCoreIn_le 2 D hx))
    (hVball (mem_map_of_mem φ hx))

/-- The beta two-root core fixes the second ball in every elementary field,
including the binary field. The Cartan-kernel condition is discharged. -/
theorem elementary_beta_actor_core_radius_two
    (hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type=true) :
    ((halfPathActor (X := (A).Universal) p 4).pCoreIn 2).map (bOne_tree_map h) ≤
      ballKernel F ((bOne_tree_cover h).vertex (p.getVert 4)) 2 ∧
    (halfPathActor (X := (A).Universal) p 4).pCoreIn 2 ≤
      ballKernel T (p.getVert 4) 2 := by
  by_cases hbinary : ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2
  · exact elementary_binary_beta_actor_core_radius_two h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT hbinary hv
  · exact original_elementary_nonbinary_actor_core_radius_two h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT hbinary
      (original_elementary_beta_cartan_kernel_ne_bot h hc hb hcomm helem
        c t htfix htmove htsq htnorm p hp hl hT hv)

/-- The actual beta actor core is central elementary and its original image
lies in Z_beta. No binary or nonbinary restriction remains. -/
theorem elementary_beta_actor_core_central
    (hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type=true) :
    let D := halfPathActor (X := (A).Universal) p 4
    pCore 2 D ≤ center D ∧ IsElementaryAbelian 2 (pCore 2 D) ∧
      (D.pCoreIn 2).map (bOne_tree_map h) ≤
        Z F ((bOne_tree_cover h).vertex (p.getVert 4)) := by
  intro D
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 4)
  let V := (D.pCoreIn 2).map φ
  have hVball : V ≤ ballKernel F v 2 :=
    (elementary_beta_actor_core_radius_two h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT hv).1
  have hVI : V ≤ neighborCoreIntersection F v := by
    apply le_iInf
    intro z
    exact CommutingTrivial.two_subgroup_le_Q F z.val (reduced_kernel_sylow h z.val)
      ((isPGroup_pCoreIn 2 D).map φ)
      (hVball.trans (ballKernel_succ_le F z.property 1))
  have hvw : (graph F).Adj v (cov.vertex (p.getVert 5)) :=
    cov.hom.map_adj (p.adj_getVert_succ (by omega))
  have hVcore : V ≤ (ballKernel F v 2).pCoreIn 2 :=
    hVI.trans_eq (reduced_neighborCoreIntersection_eq_second_core h hvw.symm)
  have hVomega : V ≤ omegaCenterIn (graphLocalGroup F v) := hVcore.trans
    (original_elementary_second_kernel_structure h hc hb hcomm helem v).2.2.1
  have hcentral : pCore 2 D ≤ center D := by
    intro x hx
    have hxV : φ x.val ∈ V := mem_map_of_mem φ (mem_map_of_mem D.subtype hx)
    have hxc := (mem_omegaCenterIn_iff _ _).mp (hVomega hxV) |>.2.1
    apply mem_center_iff.mpr
    intro y
    apply halfPathLocalMap_injective h p 4 hl
    apply Subtype.ext
    change φ (y.val*x.val)=φ (x.val*y.val)
    simp only [map_mul]
    exact mem_centralizer_iff.mp hxc _
      (halfPathActor_map_le_local h p 4 hl (mem_map_of_mem φ y.property))
  have hele : IsElementaryAbelian 2 (pCore 2 D) := by
    let f : pCore 2 D →* omegaCenterIn (graphLocalGroup F v) :=
      (φ.comp (D.subtype.comp (pCore 2 D).subtype)).codRestrict _ (fun x =>
        hVomega (mem_map_of_mem φ (mem_map_of_mem D.subtype x.property)))
    apply IsElementaryAbelian.of_injective f
    intro x y he
    apply Subtype.ext
    apply halfPathLocalMap_injective h p 4 hl
    apply Subtype.ext
    change φ x.val.val=φ y.val.val
    exact congrArg (fun z : omegaCenterIn (graphLocalGroup F v) => (z:G₀)) he
  exact ⟨hcentral,hele,hVcore.trans_eq
    ((original_elementary_second_kernel_structure h hc hb hcomm helem v).2.1 hv)⟩

/-- Central Sylow transfer removes the entire beta core from the derived
subgroup of the actual two-root actor, including the binary S3 quotient. -/
theorem elementary_beta_actor_derived_core
    (hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type=true) :
    let D := halfPathActor (X := (A).Universal) p 4
    pCore 2 D ⊓ _root_.commutator D=⊥ := by
  intro D
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let J := graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4))
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _))
    (inclusion_injective _)
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 4 hl)
  have hcentral := (elementary_beta_actor_core_central h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT hv).1
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hroots⟩ :=
    original_elementary_apartment_root_coordinates h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨hf,hker,hr,hu,z,hR,hU,hxy⟩ := hroots p hp hl hT
  let k := K ((bOne_tree_cover h).vertex (p.getVert 4)).type
  let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
  let f := (MulAut.conj z).toMonoidHom.comp
    (halfPathLinearMap h p 4 hl (e ((bOne_tree_cover h).vertex (p.getVert 4))))
  have hfk : f.ker=pCore 2 D :=
    (MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective).trans hker
  let Q := Matrix.SpecialLinearGroup.upperUnipotentSylow k 2
  let _ : IsMulCommutative Q := inferInstanceAs
    (IsMulCommutative (Matrix.SpecialLinearGroup.upperUnipotentHom k).range)
  have he := Theory.GroupTheory.CentralExtension.kernel_inf_commutator_eq_bot_of_abelian_sylow_lift
    f (by rw [hfk]; exact hcentral) (by rw [hfk]; exact pCore_isPGroup)
    Q R hR (by rw [hfk]; exact hr)
  simpa only [hfk] using he

omit c t htfix htmove htsq htnorm p hp hl hT in
/-- The literal binary quotient and the proved source valence identify the
beta-center order at every beta vertex. -/
theorem elementary_binary_beta_center_card
    (hbinary : ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (v : Vertex F) (hv : v.type=true) : Nat.card (Z F v)=2 := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  obtain ⟨m,hm,markB,_,_,hZ,_⟩ :=
    original_borel_elementary_orders_and_paths_of_source h hc hb hcomm helem
  let J := graphLocalGroup F (base F true)
  let j := J.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqJ := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  have mb : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (2^m) := markB.of_mulEquiv eqJ
  obtain ⟨k,fk,fink,hk,⟨eb⟩⟩ := mb
  let _ := fk
  let _ := fink
  let _ : Fintype k := Fintype.ofFinite k
  let _ : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let eSL : (J ⧸ pCore 2 J) ≃* SL(2,k) := eb.trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  let M : IsRankOneModel (J ⧸ pCore 2 J) := .linear m hm ⟨k,fk,fink,hk,⟨eb⟩⟩
  have hval := source_linear_neighbor_card (reduced_triple h) (reduced_borel_core_sylow h)
    (reducedFullEarlierLocalTheorems h) (source_critical_one_adjacent hc hb) M eSL
  change Nat.card ((graph F).neighborSet (base F true))=Nat.card k+1 at hval
  let cov := bOne_tree_cover h
  have he := Nat.card_congr (Equiv.ofBijective _ (cov.neighbor_bijective (base T true)))
  change Nat.card ((sourceGraph A).neighborSet (base T true)) =
    Nat.card ((graph F).neighborSet (cov.vertex (base T true))) at he
  rw [cov.vertex_base,hval,hk,
    original_elementary_binary_beta_tree_neighbor_card h hc hb hbinary] at he
  have hq : 2^m=2 := by omega
  rw [card_map_of_injective (G₀).subtype_injective,hq] at hZ
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [←hg,hv,Z_translate,card_map_of_injective (MulAut.conj g).injective]
  exact hZ

/-- The binary beta two-root actor has at most the source central involution
as its kernel, through the actual universal-to-reduced map. -/
theorem elementary_binary_beta_actor_core_card_le_two
    (hbinary : ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type=true) :
    Nat.card (pCore 2 (halfPathActor (X := (A).Universal) p 4))≤2 := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let D := halfPathActor (X := (A).Universal) p 4
  let φ := bOne_tree_map h
  let v := (bOne_tree_cover h).vertex (p.getVert 4)
  have hZ := (elementary_beta_actor_core_central h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT hv).2.2
  let f : pCore 2 D → Z F v := fun x =>
    ⟨φ x.val.val,hZ (mem_map_of_mem φ (mem_map_of_mem D.subtype x.property))⟩
  have hi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply halfPathLocalMap_injective h p 4 hl
    apply Subtype.ext
    exact congrArg (fun z : Z F v => (z : G₀)) he
  let _ : Finite (Z F v) := Finite.of_injective
    (inclusion (((source_Z_Q_U (reduced_triple h) v).1.trans (map_subtype_le _)).trans
      (Q_le_stabilizer F v)))
    (inclusion_injective _)
  have hle := Nat.card_le_card_of_injective f hi
  rw [elementary_binary_beta_center_card h hc hb hcomm helem hbinary v hv] at hle
  exact hle

/-- Reciprocal opposite-root lifts have order three or six. In the latter
case their cube is the remaining central two-element in the actual actor.
This retains the exact half-path roots and the original source quotient map. -/
theorem elementary_beta_root_pair_orders
    (hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type=true) :
    let D := halfPathActor (X := (A).Universal) p 4
    let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
    let V := (pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D
    ∀ x∈R, x≠1 → ∃ y∈V, x*x=1 ∧ y*y=1 ∧
      (orderOf (x*y)=3 ∨ orderOf (x*y)=6) ∧
      (x*y)^3∈pCore 2 D ∧ (x*y)^3∈center D := by
  intro D R V x hx hxne
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hroots⟩ :=
    original_elementary_apartment_root_coordinates h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,hker,hr,_,z,hR,hV,hxy⟩ := hroots p hp hl hT
  let k := K ((bOne_tree_cover h).vertex (p.getVert 4)).type
  let f := (MulAut.conj z).toMonoidHom.comp
    (halfPathLinearMap h p 4 hl (e ((bOne_tree_cover h).vertex (p.getVert 4))))
  have hfk : f.ker=pCore 2 D :=
    (MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective).trans hker
  obtain ⟨y,hy,hxx,hyy,hcube⟩ := hxy x hx hxne
  have himage : f (x*y)≠1 := by
    intro he
    have hsame : f x*f y=f x*f x := by
      rw [←map_mul,he,←map_mul,hxx,map_one]
    have hyx : f y=f x := mul_left_cancel hsame
    obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent k (f x)).mp
      (hR ▸ mem_map_of_mem f hx)
    obtain ⟨b,hb'⟩ := (hV (f x)).mp (hyx ▸ mem_map_of_mem f hy)
    have ha0 : a=0 := by
      have hh := congrArg (fun w : SL(2,k) => w.val 0 1) (ha.trans hb'.symm)
      simpa [Matrix.SpecialLinearGroup.transvection_coe] using hh
    apply hxne
    apply NaturalCubic.eq_one_of_root_kernel f R (by rw [hfk]; exact hr) x hx
    rw [←ha,ha0,Matrix.SpecialLinearGroup.transvection_coeff_zero]
  have himage3 : orderOf (f (x*y))=3 := orderOf_eq_prime
    (by rw [←map_pow]; exact MonoidHom.mem_ker.mp (hfk.symm ▸ hcube)) himage
  have hd3 : 3∣orderOf (x*y) := himage3 ▸ orderOf_map_dvd f (x*y)
  obtain ⟨hcentral,hele,_⟩ := elementary_beta_actor_core_central h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT hv
  have h6 : (x*y)^6=1 := by
    let _ := hele
    have hh' : ((x*y)^3)^2=1 := elemPow_eq_one_of_isElementaryAbelian ((x*y)^3) hcube
    simpa only [←pow_mul] using hh'
  have hd6 : orderOf (x*y)∣6 := orderOf_dvd_of_pow_eq_one h6
  have hcases : orderOf (x*y)=3 ∨ orderOf (x*y)=6 := order_three_or_six hd3 hd6
  exact ⟨y,hy,hxx,hyy,hcases,hcube,hcentral hcube⟩

omit c t htfix htmove htsq htnorm p hp hl hT in
/-- The original source constructs its own binary apartment. Every supported
beta actor has a central elementary kernel of order at most two, disjoint
from its derived subgroup. Reciprocal opposite-root pairs have order three or six. All original quotient and path conventions remain. -/
theorem elementary_binary_beta_central_apartment
    (hbinary : ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i=base T i) ∧
      (∀ i, t i • base T (!i)≠base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan (chosenCartans h) : Set (A).Universal)) ∧
      ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=8 →
        (∀ z∈p.support, z∈cartanApartment A (reflectionGroup (chosenCartans h) t)) →
        ((bOne_tree_cover h).vertex (p.getVert 4)).type=true →
        let D := halfPathActor (X := (A).Universal) p 4
        pCore 2 D ≤ center D ∧ IsElementaryAbelian 2 (pCore 2 D) ∧
          Nat.card (pCore 2 D)≤2 ∧ pCore 2 D ⊓ _root_.commutator D=⊥ ∧
          (D.pCoreIn 2).map (bOne_tree_map h) ≤
            Z F ((bOne_tree_cover h).vertex (p.getVert 4)) ∧
          ∀ x∈(pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D, x≠1 →
            ∃ y∈(pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D,
              x*x=1 ∧ y*y=1 ∧ (orderOf (x*y)=3 ∨ orderOf (x*y)=6) ∧
              (x*y)^3∈pCore 2 D ∧ (x*y)^3∈center D := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_binary_tree_reflections h hc hb hcomm helem hbinary (chosenCartans h)
  refine ⟨t,htfix,htmove,htsq,htnorm,?_⟩
  intro a b p hp hl hT hv D
  obtain ⟨hcentral,hele,hZ⟩ := elementary_beta_actor_core_central h hc hb hcomm helem
    (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT hv
  exact ⟨hcentral,hele,elementary_binary_beta_actor_core_card_le_two h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT hbinary hv,
    elementary_beta_actor_derived_core h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT hv,hZ,
    elementary_beta_root_pair_orders h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT hv⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
