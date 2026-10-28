module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ActorSecondKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorCentralizer

/-!
# The original strict two-root core fixes the second ball

The full source-selected Cartan and the actual two six-path radicals satisfy
radius-two propagation whenever their Cartan-kernel part is nontrivial.
The strict source constructs both nonbinary local markings and the actor's
own core quotient. The conclusion is proved on the original graph and lifted
through its universal covering. The whole local permutation kernel U is
retained; no natural-kernel or reflection-exchange premise is supplied.

Source: DGS, Groups and Graphs (1985), (14.5)(c), p.213; (14.9)(c), pp.215–216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S

/-- Under the literal nontrivial full Cartan-kernel condition, the original
strict half-path actor's own two-core fixes the radius-two ball downstairs
and upstairs. All quotient markings come from the original source. -/
theorem strict_source_small_actor_core_radius_two
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length = 12)
    (hT : ∀ z ∈ p.support,
      z ∈ strictSourceApartment h hc hne hb hβu hns hlinear)
    (hCU : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6)) ≠ ⊥) :
    ((halfPathActor (X := (A).Universal) p 6).pCoreIn 2).map (bOne_tree_map h) ≤
      ballKernel F ((bOne_tree_cover h).vertex (p.getVert 6)) 2 ∧
    (halfPathActor (X := (A).Universal) p 6).pCoreIn 2 ≤
      ballKernel T (p.getVert 6) 2 := by
  let c := chosenCartans h
  let r := strictSourceReflections h hc hne hb hβu hns hlinear
  have hfix (k) (hk : k ∈ cartan c) (j : ℕ) : k • p.getVert j = p.getVert j :=
    reflectionApartment_fixed c r.t r.normalizes k hk _ (hT _ (p.getVert_mem_support j))
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let D := halfPathActor (X := (A).Universal) p 6
  let M := D.map φ
  let V := (D.pCoreIn 2).map φ
  let v := cov.vertex (p.getVert 6)
  let w := cov.vertex (p.getVert 7)
  have hvw : (graph F).Adj v w := cov.hom.map_adj (p.adj_getVert_succ (by omega))
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  obtain ⟨K,fK,finK,chK,hfour,e,hactors⟩ :=
    strict_source_small_actor_linear_quotients h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,hker,hcover,_⟩ := hactors p hp hl hT
  have hVQ : V ≤ Q F v := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    have hxk := hker.symm ▸ hx
    rw [halfPathLinearMap_kernel] at hxk
    exact (CommutingTrivial.graphLocalGroup_core (reduced_triple h) v).le
      ⟨halfPathLocalMap h p 6 hl x,hxk,rfl⟩
  have hCD : cartan c ≤ normalizer (D : Set (A).Universal) := by
    intro k hk
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (pathRoot (X := (A).Universal) (p.drop 6) ⊔
      pathRoot (X := (A).Universal) (p.take 6)).map _ = _
    rw [Subgroup.map_sup]
    have hr := pathRoot_map_conj (p.drop 6) (p.drop 6) k rfl
      (fun j _ => by rw [drop_getVert]; exact hfix k hk _)
    have ht := pathRoot_map_conj (p.take 6) (p.take 6) k rfl
      (fun j _ => by rw [take_getVert]; exact hfix k hk _)
    exact congrArg₂ (fun R U : Subgroup (A).Universal => R ⊔ U) hr ht
  have hCN : cartan c ≤ normalizer (D.pCoreIn 2 : Set (A).Universal) :=
    hCD.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
  have hCV : C ≤ normalizer (V : Set G₀) :=
    (map_mono hCN).trans ((D.pCoreIn 2).le_normalizer_map φ)
  have hMV : M ≤ normalizer (V : Set G₀) :=
    (map_mono (D.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))).trans
        ((D.pCoreIn 2).le_normalizer_map φ)
  have hcentral : C ⊓ U F v ≤ centralizer (M : Set G₀) := by
    rintro _ ⟨⟨k,hk,rfl⟩,hkU⟩
    have hkC : k∈centralizer (D : Set (A).Universal) :=
      ((strict_source_small_actor_cartan_centralizer h hc hne hb hβu hns hlinear
        p hp hl hT).ge ⟨hk,hkU⟩).2
    apply mem_centralizer_iff.mpr
    rintro _ ⟨d,hd,rfl⟩
    exact (show Commute d k from mem_centralizer_iff.mp hkC d hd).map φ
  have hCE : C ≤ stabilizer F v ⊓ stabilizer F w := by
    rintro _ ⟨k,hk,rfl⟩
    constructor
    · change φ k • cov.vertex (p.getVert 6)=_
      rw [←cov.vertex_smul,hfix k hk 6]
    · change φ k • cov.vertex (p.getVert 7)=_
      rw [←cov.vertex_smul,hfix k hk 7]
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
  obtain ⟨hpar,_⟩ := original_bTwo_strict_path_parameters_of_linear_left
    h hc hne hb hβu hns hlinear
  have hs : sourceS (P := fun i => (P₀ L S i).subgroupOf G₀)=7 :=
    (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2.unique hpar.2
  have hVball : V ≤ ballKernel F v 2 :=
    CommutingOneProfile.source_linear_actor_subgroup_le_second_kernel (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hvw
      (sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) v (by omega))
      (e v) (e w) (hfour v.type) (hfour w.type) C M V hCE ho hd hg hVQ hCV hMV
      hcover hcentral (map_mono (pCoreIn_le 2 D)) hCU
  refine ⟨hVball,?_⟩
  intro x hx
  exact cov.ballKernel_lift (p.getVert 6) 2 x
    (halfPathActor_le_midpoint_stabilizer hl (pCoreIn_le 2 D hx))
    (hVball (mem_map_of_mem φ hx))

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
