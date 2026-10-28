module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCenterProfile
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCenterProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.CartanApartment
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenCentralizerStructure
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightHalfActor
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorElementary
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCartan
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePathProfile
public import Theory.GroupTheory.PGroup.ExtraspecialSmallOrder

/-!
# Faithful binary half-path actors in the original mixed source

The complete order-seven Cartan puts the binary actor kernel in its fixed
part of the elementary second-ball core. That fixed part is exactly the
binary center of order four. The full binary local group is centerless,
which eliminates the remaining kernel of order at most two.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorFaithful
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction Noncommuting NoncommutingProfile CommutingOneProfile CommutingNontrivial
open SourceBinaryCenterProfile


private theorem elementary_inf_extraspecial_eight {E : Type*} [Group E] [Finite E]
    (N D Z : Subgroup E) [IsElementaryAbelian 2 N] [IsExtraspecial 2 D]
    (hD : Nat.card D=8) (hZ : Nat.card Z=4) (hZN : Z≤N) (hZD : Z≤D) :
    N⊓D=Z := by
  let U := (N⊓D).subgroupOf D
  let _ : IsElementaryAbelian 2 (N⊓D : Subgroup E) := IsElementaryAbelian.of_le inf_le_left
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe (show N⊓D≤D from inf_le_right)).toMonoidHom
    (subgroupOfEquivOfLe (show N⊓D≤D from inf_le_right)).injective
  have hc := IsExtraspecial.elementary_card_lt_eight_of_card_lt_thirty_two
    (show Nat.card D<32 by omega) U
  have hd := U.card_subgroup_dvd_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show N⊓D≤D from inf_le_right)).toEquiv] at hc hd
  rw [hD] at hd
  have hlo := card_le_of_le (le_inf hZN hZD)
  rw [hZ] at hlo
  have hcard : Nat.card (N⊓D : Subgroup E)=4 := by
    interval_cases h : Nat.card (N⊓D : Subgroup E) <;> norm_num [h] at hd
    all_goals rfl
  exact (eq_of_le_of_card_ge (le_inf hZN hZD) (by omega)).symm


private theorem binary_kernel_data {G : Type*} [Group G]
    {L : Fin 2→Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (hC : Nat.card (cartan c)=7)
    (hval : ∀ v : SourceVertex (reducedAmalgam L S),
      Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet v)=if v.type then 9 else 3)
    (hpar : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7)
    (hkk : ∀ {v w : Vertex (reducedFamily L S)}, (graph (reducedFamily L S)).Adj v w →
      U (reducedFamily L S) v⊓U (reducedFamily L S) w=Q (reducedFamily L S) v⊓Q (reducedFamily L S) w)
    (hsecond : ∀ v : Vertex (reducedFamily L S), v.type=false →
      IsElementaryAbelian 2 ((ballKernel (reducedFamily L S) v 2).pCoreIn 2))
    (d : SixPathSmallActorGeometry c)
    (K : Bool→Type) [∀ i,Field (K i)] [∀ i,Finite (K i)] [∀ i,CharP (K i) 2]
    (hK : Nat.card (K false)=2)
    (e : ∀ v : Vertex (reducedFamily L S),
      (graphLocalGroup (reducedFamily L S) v ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) v)) ≃* SL(2,K v.type))
    {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b) (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection))
    (htype : (p.getVert 6).type=false) :
    let D := halfPathActor (X := (reducedAmalgam L S).Universal) p 6
    let v := (bOne_tree_cover h).vertex (p.getVert 6)
    (D.pCoreIn 2).map (bOne_tree_map h)≤(ballKernel (reducedFamily L S) v 2).pCoreIn 2 ∧
      Nat.card (pCore 2 D)≤2 ∧
      cartan c≤centralizer (D:Set (reducedAmalgam L S).Universal) ∧
      D.map (bOne_tree_map h)⊔Q (reducedFamily L S) v=graphLocalGroup (reducedFamily L S) v := by
  let A := reducedAmalgam L S
  let F := reducedFamily L S
  let v := (bOne_tree_cover h).vertex (p.getVert 6)
  let D := halfPathActor (X := A.Universal) p 6
  have hvtype : v.type=false := htype
  have hkc : Nat.card (K v.type)=2 := by rw [hvtype,hK]
  have hv : Nat.card ((sourceGraph A).neighborSet (p.getVert 6))=Nat.card (K v.type)+1 := by
    rw [hval,htype,hkc]; rfl
  have hsurj := source_six_halfPathLinearMap_surjective h c d p hp hl hT (e v) hv
  have hker := source_six_halfPathLinearMap_kernel h c d p hp hl hT (e v) hv
  have hcover := source_six_halfPathActor_supplement h c d p hp hl hT (e v) hv
  have hcentral := SourceBinaryCartan.binary_halfactor_centralization h c hC hval d p hp hl hT htype
  have hball := SourceBinaryHalfActorElementary.binary_kernel_le_second_core
    h c hC hval hpar hkk d K e p hl hT hker hcover hcentral htype
  refine ⟨hball,?_,hcentral,hcover⟩
  obtain ⟨hRk,hVk,z,hR,hV⟩ := source_six_root_coordinates h c d p hp hl hT (e v) hv
  let R := (pathRoot (X := A.Universal) (p.drop 6)).subgroupOf D
  let V := (pathRoot (X := A.Universal) (p.take 6)).subgroupOf D
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl (e v))
  let _ : ∀ i,Finite (F i) := finite_endpoints (reduced_triple h)
  let J := graphLocalGroup F v
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 6 hl)
  have hfk : f.ker=pCore 2 D :=
    (MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective).trans hker
  have hRk' : R⊓f.ker=⊥ := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective]; exact hRk
  have hVk' : V⊓f.ker=⊥ := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective]; exact hVk
  have hgen : R⊔V=⊤ := by
    rw [←subgroupOf_sup (show pathRoot (X := A.Universal) (p.drop 6)≤D from le_sup_left)
      (show pathRoot (X := A.Universal) (p.take 6)≤D from le_sup_right),subgroupOf_self]
  obtain ⟨r,x,y,_,_,_,_,_,_,_,_,_,hcore,hcard,_⟩ := binary_opposite_root_dihedral hkc f
    ((MulAut.conj z).surjective.comp hsurj) (by rw [hfk]; exact pCore_isPGroup)
    R V hgen hRk' hVk' hR hV
  rw [hfk] at hcore hcard
  let N := (ballKernel F v 2).pCoreIn 2
  let _ : IsElementaryAbelian 2 N := hsecond v hvtype
  let j : pCore 2 D→*N :=
    ((bOne_tree_map h).comp (D.subtype.comp (pCore 2 D).subtype)).codRestrict N
      (fun x => hball (mem_map_of_mem _ (mem_map_of_mem D.subtype x.property)))
  have hj : Function.Injective j := by
    intro x y heq
    apply Subtype.ext
    apply halfPathLocalMap_injective h p 6 hl
    apply Subtype.ext
    exact congrArg (fun z : N => z.val) heq
  let _ : IsElementaryAbelian 2 (pCore 2 D) := IsElementaryAbelian.of_injective j hj
  have hpow : ((x*y)^3)^2=1 := elemPow_eq_one_of_isElementaryAbelian
    ((x*y)^3) (hcore.symm ▸ mem_zpowers _)
  have hd := orderOf_dvd_of_pow_eq_one hpow
  rw [←Nat.card_zpowers,←hcore] at hd
  exact Nat.le_of_dvd (by decide) hd



section KernelElimination
variable {G : Type*} [Group G] [Finite G] {L : Fin 2→Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S

private theorem kernel_eq_bot_of_fixed_second_core (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (d : SixPathSmallActorGeometry c)
    {a b} (p : (sourceGraph A).Walk a b) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection))
    (hmid : p.getVert 6=base (Universal.cosetFamily A) false)
    (hVN : ((halfPathActor (X := (A).Universal) p 6).pCoreIn 2).map (bOne_tree_map h)≤
      (ballKernel F (base F false) 2).pCoreIn 2)
    (hVcard : Nat.card (pCore 2 (halfPathActor (X := (A).Universal) p 6))≤2)
    (hcentral : cartan c≤centralizer (halfPathActor (X := (A).Universal) p 6:Set (A).Universal))
    (hcover : (halfPathActor (X := (A).Universal) p 6).map (bOne_tree_map h)⊔Q F (base F false)=
      graphLocalGroup F (base F false))
    (hcenter : center (graphLocalGroup F (base F false))=⊥)
    (hfixed : (cartan c).map (bOne_tree_map h)≤stabilizer F (base F false) →
      (ballKernel F (base F false) 2).pCoreIn 2⊓
        centralizer ((cartan c).map (bOne_tree_map h):Set (G₀ L S))=Z F (base F false)) :
    pCore 2 (halfPathActor (X := (A).Universal) p 6)=⊥ := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let α := base F false
  let D := halfPathActor (X := (A).Universal) p 6
  let V := (D.pCoreIn 2).map φ
  let J := graphLocalGroup F α
  let C := (cartan c).map φ
  change D.map φ⊔Q F α=J at hcover
  have hv : cov.vertex (p.getVert 6)=α := by rw [hmid,cov.vertex_base]
  have hCstab : C≤stabilizer F α := by
    rintro _ ⟨k,hk,rfl⟩
    have hfix := reflectionApartment_fixed c d.reflection d.normalizes k hk _
      (hT _ (p.getVert_mem_support 6))
    change φ k • α=α
    rw [←hv,←cov.vertex_smul,hfix]
  have hfixed := hfixed hCstab
  have hCV : C≤centralizer (V:Set (G₀ L S)) := by
    rintro _ ⟨k,hk,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact (show Commute x k from mem_centralizer_iff.mp (hcentral hk) x ((pCoreIn_le 2 D) hx)).map φ
  have hVZ : V≤Z F α := (le_inf hVN (le_centralizer_iff.mp hCV)).trans_eq hfixed
  have hMV : D.map φ≤normalizer (V:Set (G₀ L S)) :=
    (map_mono (D.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))).trans
        ((D.pCoreIn 2).le_normalizer_map φ)
  have hQV : Q F α≤normalizer (V:Set (G₀ L S)) :=
    ((graph_Q_centralizes_Z (reduced_triple h) α).trans (centralizer_le hVZ)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hJV : J≤normalizer (V:Set (G₀ L S)) := hcover ▸ sup_le hMV hQV
  have hVJ : V≤J := (map_mono (pCoreIn_le 2 D)).trans (hcover ▸ le_sup_left)
  let _ : Finite (graphLocalGroup F (cov.vertex (p.getVert 6))) := inferInstance
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 6 hl)
  let _ : Finite (D.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 D)) (inclusion_injective _)
  have hvcard : Nat.card V≤2 := calc
    Nat.card V≤Nat.card (D.pCoreIn 2) := Nat.le_of_dvd Nat.card_pos ((D.pCoreIn 2).card_map_dvd φ)
    _=Nat.card (pCore 2 D) := card_map_of_injective D.subtype_injective
    _≤2 := hVcard
  have hVbot : V=⊥ := by
    by_cases he : V=⊥
    · exact he
    have hc : Nat.card V=2 := by
      have := V.one_lt_card_iff_ne_bot.mpr he
      omega
    have hCJ : J≤centralizer (V:Set (G₀ L S)) :=
      hJV.trans (normalizer_le_centralizer_of_card_two V hc)
    have hh : V≤centerIn J := le_inf hVJ (le_centralizer_iff.mp hCJ)
    rw [centerIn_eq_map_center,hcenter,Subgroup.map_bot] at hh
    exact bot_unique hh
  apply bot_unique
  intro x hx
  have hxφ : φ (x:D)=1 := hVbot.le (mem_map_of_mem φ (mem_map_of_mem D.subtype hx))
  change x=1
  apply halfPathLocalMap_injective h p 6 hl
  apply Subtype.ext
  change φ (x:D)=φ (1 : (A).Universal)
  exact hxφ.trans (map_one φ).symm

end KernelElimination


section PairKernel
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "L" => ![U,K]
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
private theorem pair_kernel_eq_bot (hF : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (c : CompatibleCartans L (reducedSylow L S)) (hC : Nat.card (cartan c)=7)
    (hval : ∀ v : SourceVertex A, Nat.card ((sourceGraph A).neighborSet v)=if v.type then 9 else 3)
    (hpar : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7)
    (hkk : ∀ {v w : Vertex F}, (graph F).Adj v w → ChapterF.Source.DGS85.U F v⊓ChapterF.Source.DGS85.U F w=Q F v⊓Q F w)
    (hsecond : ∀ v : Vertex F, v.type=false → IsElementaryAbelian 2 ((ballKernel F v 2).pCoreIn 2))
    (d : SixPathSmallActorGeometry c) {a b} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection))
    (hmid : p.getVert 6=base (Universal.cosetFamily A) false)
    (hfixed : Nat.card (Z F (base F false))=4 → Z F (base F false)≤(ballKernel F (base F false) 2).pCoreIn 2 →
      (cartan c).map (bOne_tree_map hF.swap)≤stabilizer F (base F false) →
        (ballKernel F (base F false) 2).pCoreIn 2⊓
          centralizer ((cartan c).map (bOne_tree_map hF.swap):Set (G₀ L S))=Z F (base F false)) :
    pCore 2 (halfPathActor (X := (A).Universal) p 6)=⊥ := by
  let h := hF.swap
  let cov := bOne_tree_cover h
  let α := base F false
  have hv : cov.vertex (p.getVert 6)=α := by rw [hmid,cov.vertex_base]
  have ht : (p.getVert 6).type=false := by rw [hmid]; rfl
  let em (v : Vertex F) : (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃*
      SL(2,pathFields v.type) := (Assembly.linear_graph_quotient h v.type
        (path_field_markings eK eU v.type) v rfl).some
  obtain ⟨hVN,hVcard,hcentral,hcover⟩ := binary_kernel_data h c hC hval hpar hkk hsecond
    d pathFields (by change Nat.card (ZMod 2)=2; exact Nat.card_zmod 2) em p hp hl hT ht
  change ((halfPathActor (X := (A).Universal) p 6).pCoreIn 2).map (bOne_tree_map h)≤
    (ballKernel F (cov.vertex (p.getVert 6)) 2).pCoreIn 2 at hVN
  rw [hv] at hVN hcover
  obtain ⟨hz,hZN,hcenter⟩ := pair_binary_center hF eK eU
  exact kernel_eq_bot_of_fixed_second_core h c d p hl hT hmid hVN hVcard hcentral hcover hcenter
    (hfixed hz hZN)
end PairKernel

private theorem cartan_map_le_binary_stabilizer {G : Type*} [Group G]
    {L : Fin 2→Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) :
    (cartan c).map (bOne_tree_map h)≤stabilizer (reducedFamily L S) (base (reducedFamily L S) false) := by
  let A := reducedAmalgam L S
  let UP := Universal.cosetFamily A
  let F := reducedFamily L S
  have hmapE : (originalMiddle A).map (bOne_tree_map h)=F false⊓F true := by
    rw [show originalMiddle A=UP false⊓UP true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact (bOne_tree_cover h).map_inf
  have hh : (cartan c).map (bOne_tree_map h)≤F false :=
    (map_mono (cartan_le c)).trans (hmapE ▸ inf_le_left)
  simpa only [Subgroup.CosetGeometry.stabilizer_base] using hh

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
private theorem source_binary_fixed_second_core
    (h : HypothesisF11 Lₛ Sₛ)
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ))
    (hz : Nat.card (Z Fₛ (base Fₛ false))=4)
    (hZN : Z Fₛ (base Fₛ false)≤(ballKernel Fₛ (base Fₛ false) 2).pCoreIn 2)
    (hCstab : (cartan c).map
      (bOne_tree_map h)≤
        stabilizer Fₛ (base Fₛ false)) :
    (ballKernel Fₛ (base Fₛ false) 2).pCoreIn 2 ⊓
      centralizer (((cartan c).map
        (bOne_tree_map h)):
          Set (G₀ Lₛ Sₛ)) = Z Fₛ (base Fₛ false) := by
  let ι := (G₀ Lₛ Sₛ).subtype
  let φ := bOne_tree_map h
  let α := base Fₛ false
  let β := base Fₛ true
  let N := (ballKernel Fₛ α 2).pCoreIn 2
  let Z₀ := Z Fₛ α
  let C := (cartan c).map φ
  let C₀ := c.D 0⊔c.D 1
  let E := H.pCoreIn 2⊓centralizer (C₀:Set G)
  have hCmap : C.map ι=C₀ := by
    rw [Subgroup.map_map]
    exact SourceEightHalfActor.original_cartan_image hG T hempty hM hu hmany hcard e H hH eR c
  have hCH : C₀≤H := by
    have hh := c.joint_le.trans ((reduced_commonBorel_le h).trans
      (commonBorel_le_parabolic (L := Lₛ) (S := Sₛ) 1))
    change C₀≤parabolic (locals T M Mc H) Sₛ 0 at hh
    rwa [(source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1] at hh
  have hC7 : Nat.card C₀=7 := by
    have hh := SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c
    rw [cartan,card_map_of_injective middleMap_injective,
      Nat.card_congr (subgroupOfEquivOfLe c.joint_le).toEquiv] at hh
    exact hh
  obtain ⟨_,hE,hex⟩ := SourceSevenCentralizerStructure.source_seven_fixed_core_structure
    hG T hempty hM hu hmany hcard e H hH eR C₀ hCH hC7
  let _ : IsExtraspecial 2 E := hex
  let _ : ∀ i,Finite (Fₛ i) := finite_endpoints (reduced_triple h)
  have hCnZ : C≤normalizer (Z₀:Set (G₀ Lₛ Sₛ)) := hCstab.trans
    ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer Fₛ α)).mp (Z_normal Fₛ α))
  have hC₀nZ : C₀≤normalizer (Z₀.map ι:Set G) := by
    rw [←hCmap]
    exact (map_mono hCnZ).trans (Z₀.le_normalizer_map ι)
  have hZcard : Nat.card (Z₀.map ι)=4 := by
    rw [card_map_of_injective (G₀ Lₛ Sₛ).subtype_injective]; exact hz
  have hZC : Z₀.map ι≤centralizer (C₀:Set G) :=
    seven_centralizes_four C₀ (Z₀.map ι) hC7 hZcard hC₀nZ
  have hab : (graph Fₛ).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hNQ : N≤Q Fₛ β := by
    rw [show N=(ballKernel Fₛ α 2).pCoreIn 2 from rfl,
      ←reduced_neighborCoreIntersection_eq_second_core h hab.symm]
    exact neighborCoreIntersection_le Fₛ hab.symm
  have hQmap : (Q Fₛ β).map ι=H.pCoreIn 2 := by
    have hh := reduced_base_Q_map h true
    change (Q Fₛ β).map ι=(parabolic (locals T M Mc H) Sₛ 0).pCoreIn 2 at hh
    rwa [(source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1] at hh
  have hNmap : N.map ι≤H.pCoreIn 2 := hQmap ▸ map_mono hNQ
  let _ : IsElementaryAbelian 2 N :=
    SourceBinarySecondCore.source_binary_second_core hG T hempty hM hu hmany hcard e H hH eR α rfl
  let _ : IsElementaryAbelian 2 (N.map ι) := IsElementaryAbelian.map ι
  have hfixed : N.map ι⊓E=Z₀.map ι := elementary_inf_extraspecial_eight
    (N.map ι) E (Z₀.map ι) hE hZcard (map_mono hZN)
    (le_inf ((map_mono hZN).trans hNmap) hZC)
  apply Subgroup.map_injective (G₀ Lₛ Sₛ).subtype_injective
  rw [←map_inf_centralizer_of_injective ι (G₀ Lₛ Sₛ).subtype_injective,hCmap]
  change N.map ι⊓centralizer (C₀:Set G)=Z₀.map ι
  calc
    N.map ι⊓centralizer (C₀:Set G)=N.map ι⊓E := by
      change _=N.map ι⊓(H.pCoreIn 2⊓centralizer (C₀:Set G))
      rw [←inf_assoc,inf_eq_left.mpr hNmap]
    _=Z₀.map ι := hfixed



set_option maxHeartbeats 800000 in
/-- The full elementary binary second-ball core fixed by the whole original
Cartan is exactly the original binary center plane, in the ambient group. -/
theorem source_binary_second_core_cartan_fixed
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) :
    ((ballKernel Fₛ (base Fₛ false) 2).pCoreIn 2).map (G₀ Lₛ Sₛ).subtype ⊓
      centralizer ((c.D 0⊔c.D 1 : Subgroup G):Set G) =
        (Z Fₛ (base Fₛ false)).map (G₀ Lₛ Sₛ).subtype := by
  let h : HypothesisF11 Lₛ Sₛ := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  let ι := (G₀ Lₛ Sₛ).subtype
  let C := (cartan c).map (bOne_tree_map h)
  obtain ⟨hz,hZN,_⟩ := source_binary_center_profile hG T hempty hM hu hmany hcard e H hH eR
  have hf := source_binary_fixed_second_core hG T hempty hM hu hmany hcard e H hH eR
    h c hz hZN (cartan_map_le_binary_stabilizer h c)
  have hCmap : C.map ι=c.D 0⊔c.D 1 := by
    rw [Subgroup.map_map]
    exact SourceEightHalfActor.original_cartan_image hG T hempty hM hu hmany hcard e H hH eR c
  rw [←hCmap,map_inf_centralizer_of_injective ι (G₀ Lₛ Sₛ).subtype_injective]
  exact congrArg (Subgroup.map ι) hf


set_option maxHeartbeats 800000 in
/-- Every supported binary-centered twelve-path in the supplied original
geometry has faithful canonical half-path actor. The full Cartan and the
entire intrinsic actor two-core are retained. -/
theorem source_binary_halfactor_core_eq_bot
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ))
    (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex Aₛ} (p : (sourceGraph Aₛ).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment Aₛ (reflectionGroup c d.reflection))
    (hmid : p.getVert 6=base (Universal.cosetFamily Aₛ) false) :
    pCore 2 (halfPathActor (X := (Aₛ).Universal) p 6)=⊥ := by
  obtain ⟨eU⟩ := source_binary_marking hG T hempty hM hu hmany hcard e H hH eR
  have hF : HypothesisF11 ![locals T M Mc H 0,locals T M Mc H 1] Sₛ :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  let eK : (locals T M Mc H 0 ⧸ pCore 2 (locals T M Mc H 0)) ≃* Theory.PSL2.BinaryGroup 3 :=
    residualQuotientEquiv H eR
  have hC := SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c
  exact pair_kernel_eq_bot (G := G) (K := locals T M Mc H 0) (U := locals T M Mc H 1) (S := Sₛ) hF eK eU c hC
    (SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR)
    (source_path_profile hG T hempty hM hu hmany hcard e H hH eR).1
    (fun {_ _} hw => SourceLocalKernels.source_adjacent_kernel_intersection
      hG T hempty hM hu hmany hcard e H hH eR hw)
    (SourceBinarySecondCore.source_binary_second_core hG T hempty hM hu hmany hcard e H hH eR)
    d p hp hl hT hmid
    (fun hz hZN hCstab => source_binary_fixed_second_core hG T hempty hM hu hmany hcard e H hH eR
      hF.swap c hz hZN hCstab)


end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorFaithful
