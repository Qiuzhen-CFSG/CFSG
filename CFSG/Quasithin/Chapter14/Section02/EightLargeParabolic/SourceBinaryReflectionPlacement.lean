module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCartanFixedCore
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorFaithful
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathMidpointCoordinates
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCenterProfile
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCartan
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePathProfile

/-!
# The original binary reflection belongs to its half-path actor

The canonical actor is a complement to the entire binary core. Its whole
Cartan centralizes that actor and fixes exactly the binary center plane in
the core. A reflection normalizing both consequently has central core
component, which vanishes in the centerless binary local group.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryReflectionPlacement
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction Noncommuting NoncommutingProfile CommutingOneProfile CommutingNontrivial

private theorem normalizing_disjoint_centralizes {G : Type*} [Group G]
    (A B : Subgroup G) (hn : A≤normalizer (B:Set G)) (hd : Disjoint A B) :
    B⊓normalizer (A:Set G)≤centralizer (A:Set G) := by
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  apply (le_inf ?_ ?_).trans (disjoint_iff.mp hd).le
  · exact le_normalizer_iff_commutator_le_left.mp inf_le_right
  · exact (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp hn)

private theorem normalizer_cartan_complement {G : Type*} [Group G]
    (D Q C J : Subgroup G) (hgen : D⊔Q=J)
    (hJQ : J≤normalizer (Q:Set G)) (hDQ : Disjoint D Q)
    (hCD : C≤centralizer (D:Set G)) (hCQ : C≤normalizer (Q:Set G))
    (hCQdis : Disjoint C Q) (hfixed : Q⊓centralizer (C:Set G)≤centerIn Q)
    (hcenter : center J=⊥) (x : G) (hxJ : x∈J)
    (hxD : x∈normalizer (D:Set G)) (hxC : x∈normalizer (C:Set G)) : x∈D := by
  have hDJ : D≤J := hgen ▸ le_sup_left
  have hQJ : Q≤J := hgen ▸ le_sup_right
  have hprod : (J:Set G)=(D:Set G)*(Q:Set G) := by
    rw [←hgen]
    exact coe_mul_of_left_le_normalizer_right D Q (hDJ.trans hJQ)
  obtain ⟨d,hd,q,hq,hdq⟩ := hprod ▸ (show x∈(J:Set G) from hxJ)
  change d*q=x at hdq
  have hqe : q=d⁻¹*x := by rw [←hdq,inv_mul_cancel_left]
  have hqD : q∈normalizer (D:Set G) := by
    rw [hqe]
    exact (normalizer (D:Set G)).mul_mem ((normalizer (D:Set G)).inv_mem (D.le_normalizer hd)) hxD
  have hqC : q∈normalizer (C:Set G) := by
    rw [hqe]
    exact (normalizer (C:Set G)).mul_mem ((normalizer (C:Set G)).inv_mem
      (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hCD hd))) hxC
  have hqCD := normalizing_disjoint_centralizes D Q (hDJ.trans hJQ) hDQ ⟨hq,hqD⟩
  have hqCC := normalizing_disjoint_centralizes C Q hCQ hCQdis ⟨hq,hqC⟩
  have hqCQ : q∈centralizer (Q:Set G) := (hfixed ⟨hq,hqCC⟩).2
  have hqCJ : q∈centralizer (J:Set G) := by
    apply (le_centralizer_iff.mp ?_ : zpowers q≤centralizer (J:Set G)) (mem_zpowers q)
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mpr (zpowers_le.mpr hqCD))
      (le_centralizer_iff.mpr (zpowers_le.mpr hqCQ))
  have hqZ : q∈centerIn J := ⟨hQJ hq,hqCJ⟩
  rw [centerIn_eq_map_center,hcenter,Subgroup.map_bot] at hqZ
  have hq1 : q=1 := hqZ
  rw [hq1,mul_one] at hdq
  exact hdq ▸ hd

private theorem reflection_mem_actor {G : Type*} [Group G]
    {L : Fin 2→Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (d : SixPathSmallActorGeometry c)
    {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b) (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support,z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)))) ≃* SL(2,k))
    (hval : Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet (p.getVert 6))=Nat.card k+1)
    (hcore : pCore 2 (halfPathActor (X := (reducedAmalgam L S).Universal) p 6)=⊥)
    (hcentral : cartan c≤centralizer (halfPathActor (X := (reducedAmalgam L S).Universal) p 6:Set (reducedAmalgam L S).Universal))
    (hfixed : Q (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6))⊓
      centralizer ((cartan c).map (bOne_tree_map h):Set (G₀ L S))≤
      centerIn (Q (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6))))
    (hcenter : center (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)))=⊥)
    (x : (reducedAmalgam L S).Universal) (hx2 : x*x=1)
    (hxC : x∈normalizer (cartan c:Set (reducedAmalgam L S).Universal))
    (hrev : ∀ j≤12,x•p.getVert j=p.getVert (12-j)) :
    x∈halfPathActor (X := (reducedAmalgam L S).Universal) p 6 := by
  let A := reducedAmalgam L S
  let F := reducedFamily L S
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let D := halfPathActor (X := A.Universal) p 6
  let M := D.map φ
  let C := (cartan c).map φ
  let v := cov.vertex (p.getVert 6)
  let J := graphLocalGroup F v
  let _ : ∀ i,Finite (F i) := finite_endpoints (reduced_triple h)
  have hgen : M⊔Q F v=J := source_six_halfPathActor_supplement h c d p hp hl hT e hval
  have hker : (halfPathLinearMap h p 6 hl e).ker=⊥ :=
    (source_six_halfPathLinearMap_kernel h c d p hp hl hT e hval).trans hcore
  have hMQ : Disjoint M (Q F v) := by
    apply disjoint_def.mpr
    rintro z ⟨y,hy,rfl⟩ hz
    let yD : D := ⟨y,hy⟩
    have hycore : halfPathLocalMap h p 6 hl yD∈pCore 2 J := by
      have hh : J.pCoreIn 2=Q F v := CommutingTrivial.graphLocalGroup_core (reduced_triple h) v
      obtain ⟨w,hw,he⟩ := hh.ge hz
      have hw' : w=halfPathLocalMap h p 6 hl yD := Subtype.ext he
      exact hw' ▸ hw
    have hyker : yD∈(halfPathLinearMap h p 6 hl e).ker := by
      rw [halfPathLinearMap_kernel]
      exact hycore
    have hy1 : yD=1 := hker.le hyker
    have hy1' : y=1 := congrArg (fun u : D => (u:A.Universal)) hy1
    rw [hy1',map_one]
  have hCD : C≤centralizer (M:Set (G₀ L S)) :=
    (map_mono hcentral).trans (map_centralizer_le_centralizer_image _ _)
  have hCv : C≤stabilizer F v := by
    rintro _ ⟨a,ha,rfl⟩
    change φ a•cov.vertex (p.getVert 6)=_
    rw [←cov.vertex_smul,reflectionApartment_fixed c d.reflection d.normalizes a ha _
      (hT _ (p.getVert_mem_support 6))]
  have hCQ : C≤normalizer (Q F v:Set (G₀ L S)) := hCv.trans (stabilizer_normalizes_Q F v)
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite (Q F v) := Finite.of_injective (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  have hCQdis : Disjoint C (Q F v) := by
    have hQ : IsPGroup 2 (Q F v) := isPGroup_pCoreIn 2 _
    obtain ⟨r,hr⟩ := hQ.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hxfix : x•p.getVert 6=p.getVert 6 := hrev 6 (by decide)
  have hxv : φ x∈stabilizer F v := by
    change φ x•cov.vertex (p.getVert 6)=_
    rw [←cov.vertex_smul,hxfix]
  have hxJ : φ x∈J := by
    have hpow : φ x^(2^1)=1 := by rw [pow_one,pow_two,←map_mul,hx2,map_one]
    exact pGroup_le_sylowGenerated (stabilizer F v) (zpowers (φ x)) (zpowers_le.mpr hxv)
      (IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hpow))
      (mem_zpowers _)
  have hxD : x∈normalizer (D:Set A.Universal) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (pathRoot (X := A.Universal) (p.drop 6)⊔pathRoot (X := A.Universal) (p.take 6)).map _=_
    rw [Subgroup.map_sup]
    obtain ⟨ha,hb⟩ := pathRoot_halves_reflection p 6 hl x hrev
    exact (congrArg₂ (fun R V : Subgroup A.Universal => R⊔V) hb ha).trans (sup_comm _ _)
  have hxM : φ x∈M := normalizer_cartan_complement M (Q F v) C J hgen
    ((sylowGenerated_le _).trans (stabilizer_normalizes_Q F v)) hMQ hCD hCQ hCQdis hfixed hcenter
    (φ x) hxJ (D.le_normalizer_map φ (mem_map_of_mem φ hxD))
    ((cartan c).le_normalizer_map φ (mem_map_of_mem φ hxC))
  obtain ⟨y,hy,he⟩ := hxM
  have hh := (cov.stabilizerEquiv (p.getVert 6)).injective
    (a₁ := ⟨y,halfPathActor_le_midpoint_stabilizer hl hy⟩) (a₂ := ⟨x,hxfix⟩) (Subtype.ext he)
  have hyx : y=x := congrArg Subtype.val hh
  exact hyx ▸ hy

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
local notation "Fₛ" => reducedFamily Lₛ Sₛ

local notation "Aₛ" => reducedAmalgam Lₛ Sₛ

set_option maxHeartbeats 800000 in
/-- The same Cartan-normalizing involution reversing an actual supported
binary-centered twelve-path already belongs to its full half-path actor. -/
theorem source_binary_reflection_mem_halfactor
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ))
    (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex Aₛ} (p : (sourceGraph Aₛ).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support,z∈cartanApartment Aₛ (reflectionGroup c d.reflection))
    (hmid : p.getVert 6=base (Universal.cosetFamily Aₛ) false)
    (x : (Aₛ).Universal) (hx2 : x*x=1)
    (hxC : x∈normalizer (cartan c:Set (Aₛ).Universal))
    (hrev : ∀ j≤12,x•p.getVert j=p.getVert (12-j)) :
    x∈halfPathActor (X := (Aₛ).Universal) p 6 := by
  let h : HypothesisF11 Lₛ Sₛ := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 6)
  have hv : v=base Fₛ false := by rw [show v=cov.vertex (p.getVert 6) from rfl,hmid,cov.vertex_base]
  have ht : (p.getVert 6).type=false := by rw [hmid]; rfl
  have hvt : v.type=false := ht
  obtain ⟨eU⟩ := SourceBinaryCenterProfile.source_binary_marking hG T hempty hM hu hmany hcard e H hH eR
  let eK : (locals T M Mc H 0 ⧸ pCore 2 (locals T M Mc H 0)) ≃* Theory.PSL2.BinaryGroup 3 :=
    residualQuotientEquiv H eR
  let em : (graphLocalGroup Fₛ v ⧸ pCore 2 (graphLocalGroup Fₛ v)) ≃*
      SL(2,pathFields v.type) := (Assembly.linear_graph_quotient h v.type
        (path_field_markings (K := locals T M Mc H 0) (U := locals T M Mc H 1) eK eU v.type) v rfl).some
  have hval : Nat.card ((sourceGraph Aₛ).neighborSet (p.getVert 6))=Nat.card (pathFields v.type)+1 := by
    rw [SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR,ht,hvt]
    change 3=Nat.card (ZMod 2)+1
    rw [Nat.card_zmod]
  have hcore := SourceBinaryHalfActorFaithful.source_binary_halfactor_core_eq_bot
    hG T hempty hM hu hmany hcard e H hH eR c d p hp hl hT hmid
  have hcentral := SourceBinaryCartan.binary_halfactor_centralization h c
    (SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c)
    (SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR)
    d p hp hl hT ht
  have hfixed : Q Fₛ v⊓centralizer ((cartan c).map (bOne_tree_map h):Set (G₀ Lₛ Sₛ))≤centerIn (Q Fₛ v) := by
    rw [hv]
    have he := SourceBinaryCartanFixedCore.source_binary_core_cartan_fixed
      hG T hempty hM hu hmany hcard e H hH eR c
    change Q Fₛ (base Fₛ false)⊓centralizer ((cartan c).map (bOne_tree_map h):Set (G₀ Lₛ Sₛ))=
      Z Fₛ (base Fₛ false) at he
    rw [he]
    exact le_inf (he.symm.le.trans inf_le_left)
      (le_centralizer_iff.mp (graph_Q_centralizes_Z (reduced_triple h) (base Fₛ false)))
  have hcenter : center (graphLocalGroup Fₛ v)=⊥ := by
    rw [hv]
    exact (SourceBinaryCenterProfile.source_binary_center_profile hG T hempty hM hu hmany hcard e H hH eR).2.2
  exact reflection_mem_actor h c d p hp hl hT em hval hcore hcentral hfixed hcenter x hx2 hxC hrev

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryReflectionPlacement
