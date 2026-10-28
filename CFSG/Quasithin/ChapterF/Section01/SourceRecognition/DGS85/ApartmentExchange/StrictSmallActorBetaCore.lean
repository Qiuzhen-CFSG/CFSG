module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorPerfect
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorSecondKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictBetaSecondCore
public import Theory.GroupTheory.Commutator.AbelianSylowLift

/-!
# Vanishing of the strict two-root core at beta

The source identifies beta's second-kernel two-core with its central Z.
Radius-two propagation puts the smaller actor's own core in that center.
The actor is perfect and its original path root is an injective abelian
Sylow lift. Central Sylow transfer therefore kills the whole smaller core.
The literal nontrivial full Cartan-kernel condition is retained.

Source: DGS, Groups and Graphs (1985), (14.9)(a), pp.215–216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups IsMulCommutative
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

/-- The actual beta-midpoint smaller actor is core-free under the literal
nontrivial full Cartan-kernel condition. -/
theorem strict_source_small_actor_beta_core_eq_bot
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)
    (hCU : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6))≠⊥)
    (htype : ((bOne_tree_cover h).vertex (p.getVert 6)).type=true) :
    pCore 2 (halfPathActor (X := (A).Universal) p 6)=⊥ := by
  let D := halfPathActor (X := (A).Universal) p 6
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 6)
  let J := graphLocalGroup F v
  let V := (D.pCoreIn 2).map φ
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 6 hl)
  let _ := strict_source_small_actor_perfect h hc hne hb hβu hns hlinear p hp hl hT
  have hbase : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hZcentral := reduced_bTwo_middle_central h hc hne hb hbase hβu
  have hβ := (strict_source_beta_second_core h hc hne hb hβu hns hlinear).2.1
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  have hsecond : (ballKernel F v 2).pCoreIn 2=Z F v := by
    rw [←hg,ballKernel_translate,AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (MulAut.conj g).injective,htype,hβ,←Z_translate]
  have hVball : V≤ballKernel F v 2 :=
    (strict_source_small_actor_core_radius_two h hc hne hb hβu hns hlinear p hp hl hT hCU).1
  have hVI : V≤CommutingOneProfile.neighborCoreIntersection F v := by
    apply le_iInf
    intro z
    exact CommutingTrivial.two_subgroup_le_Q F z.val (reduced_kernel_sylow h z.val)
      ((isPGroup_pCoreIn 2 D).map φ)
      (hVball.trans (ballKernel_succ_le F z.property 1))
  have hvw : (graph F).Adj v (cov.vertex (p.getVert 7)) :=
    cov.hom.map_adj (p.adj_getVert_succ (by omega))
  have hVZ : V≤Z F v := hVI.trans_eq
    ((CommutingOneProfile.reduced_neighborCoreIntersection_eq_second_core h hvw.symm).trans hsecond)
  have hcent : Z F v≤centralizer (J : Set (G₀ L S)) := by
    rw [←hg,htype,Z_translate]
    rintro _ ⟨z,hz,rfl⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    change y∈graphLocalGroup F v at hy
    rw [←hg,htype] at hy
    have hJg : graphLocalGroup F (g • base F true) =
        (graphLocalGroup F (base F true)).map (MulAut.conj g).toMonoidHom :=
      graphLocalGroup_conjugate (reduced_triple h) g (base F true)
    rw [hJg] at hy
    obtain ⟨a,ha,rfl⟩ := hy
    have hzC := (hZcentral hz).2
    exact (show Commute a z from mem_centralizer_iff.mp hzC a ha).map (MulAut.conj g).toMonoidHom
  have hcentral : pCore 2 D≤center D := by
    intro x hx
    have hxV : φ x.val∈V := mem_map_of_mem φ (mem_map_of_mem D.subtype hx)
    apply mem_center_iff.mpr
    intro y
    apply halfPathLocalMap_injective h p 6 hl
    apply Subtype.ext
    change φ (y.val*x.val)=φ (x.val*y.val)
    simp only [map_mul]
    exact mem_centralizer_iff.mp (hcent (hVZ hxV)) _
      (halfPathActor_map_le_local h p 6 hl (mem_map_of_mem φ y.property))
  obtain ⟨K,fK,finK,chK,hK,e,hmarks⟩ :=
    strict_source_small_actor_marked_coordinates h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,hker,hRk,_,z,hR,_⟩ := hmarks p hp hl hT
  let k := K v.type
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl (e v))
  have hfk : f.ker=pCore 2 D :=
    (MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective).trans hker
  let R := (pathRoot (X := (A).Universal) (p.drop 6)).subgroupOf D
  let Q := Matrix.SpecialLinearGroup.upperUnipotentSylow k 2
  let _ : IsMulCommutative Q := inferInstanceAs
    (IsMulCommutative (Matrix.SpecialLinearGroup.upperUnipotentHom k).range)
  have he := CentralExtension.kernel_inf_commutator_eq_bot_of_abelian_sylow_lift
    f (by rw [hfk]; exact hcentral) (by rw [hfk]; exact pCore_isPGroup)
    Q R hR (by
      rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective]
      exact hRk)
  simpa only [hfk,Group.IsPerfect.commutator_eq_top,inf_top_eq] using he

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
