module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ActorSecondKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorCartan

/-!
# The elementary two-root core fixes the second ball

For every supported eight-path, the actual opposite four-path radicals
supplement the midpoint core. The full Cartan normalizes their join and
centralizes it precisely on its full local-kernel part. The original
nonbinary elementary source supplies both linear fields, so the radius-two
propagation theorem applies to this join's own two-core. The conclusion is
proved downstairs and lifted through the original covering on stabilizers.

The final source application constructs the same-Cartan reflections and
apartment without local catalogue or reflection assumptions. It retains the
nontrivial Cartan-kernel condition from (14.5)(c). This is control of the
two-root actor: adjoining a suitably chosen reflection, eliminating its
core, exchange, root signs, binary choices and the nonelementary catalogue
and marked-assembly obligations are not consequences asserted here.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175;
(14.3), p.212, and (14.5)(b)--(c), p.213.
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

/-- The actual two-root core fixes the radius-two ball whenever the
Cartan's full local-kernel part is nontrivial (the two-root clause of 14.5(c)). -/
theorem original_elementary_nonbinary_actor_core_radius_two
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hne : (cartan c).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥) :
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
  have hm2 : 2 ≤ m := by
    by_contra hn
    have he : m=1 := by omega
    apply hnb
    let J := graphLocalGroup F (base F true)
    let j := J.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
    refine ⟨K true,inferInstance,inferInstance,?_,?_⟩
    · simpa only [he,ite_true,Nat.mul_one,Nat.pow_one] using hK true
    · exact ⟨(QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).symm.trans
        ((e (base F true)).trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL : SL(2,K true) ≃* PSL(2,K true)))⟩
  have hfour (i : Bool) : 4 ≤ Nat.card (K i) := by
    rw [hK]
    apply (show 2^2 ≤ 2^(if i then m else 2*m) from
      Nat.pow_le_pow_right (by decide) ?_)
    cases i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
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
  have hVball : V ≤ ballKernel F v 2 :=
    source_linear_actor_subgroup_le_second_kernel (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hvw
      (sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) v (by omega))
      (e v) (e w) (hfour v.type) (hfour w.type) C M V hCE ho hd hg hVQ hCV hMV
      hcover hcentral (map_mono (pCoreIn_le 2 D)) hne
  refine ⟨hVball,?_⟩
  intro x hx
  exact cov.ballKernel_lift (p.getVert 4) 2 x
    (halfPathActor_le_midpoint_stabilizer hl (pCoreIn_le 2 D hx))
    (hVball (mem_map_of_mem φ hx))

omit c t htfix htmove htsq htnorm p hp hl hT in
/-- The original nonbinary elementary source supplies the same-Cartan
apartment and the radius-two core conclusion, with no reflection or local
catalogue premise. The nontrivial kernel clause is exactly that in 14.5(c). -/
theorem original_elementary_nonbinary_second_kernel_apartment
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i=base T i) ∧
      (∀ i, t i • base T (!i)≠base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan (chosenCartans h) : Set (A).Universal)) ∧
      ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=8 →
        (∀ z∈p.support, z∈cartanApartment A (reflectionGroup (chosenCartans h) t)) →
        (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
          U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥ →
        ((halfPathActor (X := (A).Universal) p 4).pCoreIn 2).map (bOne_tree_map h) ≤
          ballKernel F ((bOne_tree_cover h).vertex (p.getVert 4)) 2 ∧
        (halfPathActor (X := (A).Universal) p 4).pCoreIn 2 ≤
          ballKernel T (p.getVert 4) 2 := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb (chosenCartans h)
  exact ⟨t,htfix,htmove,htsq,htnorm,fun p hp hl hT hne =>
    original_elementary_nonbinary_actor_core_radius_two h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT hnb hne⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
