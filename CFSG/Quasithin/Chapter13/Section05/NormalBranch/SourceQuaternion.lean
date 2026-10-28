module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreCollapse
public import Theory.Representation.BinaryPermutation.FiveLowRank.SubgroupBounds
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion
public import Theory.GroupTheory.QuaternionCentralProductQuotient

/-!
# The original normal-branch quaternion core

The collapsed K-core makes the U_H image of order four have kernel V₃,
so |U_H|=32. A pointwise seed fixer acts trivially on the genuine five-point
core; local irreducibility then gives Z(U_H)=V₁. The original Frattini
bound makes U_H extraspecial, and its elementary eight-subgroup selects
the plus type, producing actual commuting quaternion factors.

Sylow maximality in the literal A₅ image also proves O₂(L₁)=U_H. The
final source consumer chooses the original collapsed pair internally,
so it assumes no core collapse, quaternion or block conclusion.

Source: Aschbacher–Smith,13.5.15(5), printed p.920, via G.2.4(8),p.335.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceQuaternion
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceFiveModule SourceUpperStructure SourceUpperAction SourceUpperBorel SourceCoreCollapse
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

theorem actor_eq_one_of_seed_centralizer
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val≤D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (k : NormalBranch.K D g.val) (hk : k.val∈centralizer (D.Vplus:Set G)) :
    restrictedActor d hK a hi k=1 := by
  let A := (D.Vplus.subgroupOf D.V).map (moduleEquiv d a).toMonoidHom
  have hc : Nat.card A=8 := by
    rw [card_map_of_injective (moduleEquiv d a).injective,
      Nat.card_congr (subgroupOfEquivOfLe d.seed_le).toEquiv,d.seed_card]
  apply BinaryPermutation.FiveLowRank.eq_one_of_fixes_eight _ A hc
  rintro _ ⟨v,hv,rfl⟩
  have he := moduleEquiv_equivariant d hK a hi e k v
  rw [quotientEquiv_mk] at he
  have hfix : D.V.normalizerMonoidHom
      ⟨k.val,d.normalizes_V (mem_sup_left (hK k.property))⟩ v=v := by
    apply Subtype.ext
    change k.val*v.val*k.val⁻¹=v.val
    rw [←hk v.val hv,mul_inv_cancel_right]
  rw [hfix] at he
  exact he.symm

theorem closure_card (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val≤D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V) : Nat.card D.UH=32 := by
  let J := NormalBranch.K D g.val
  let hUK : D.UH≤J := le_sup_left
  let f := restrictedActor d hK a hi
  let q := f.comp (inclusion hUK)
  have hr : q.range=(D.UH.subgroupOf J).map f := by
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨inclusion hUK u,u.property,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k.val,hk⟩,rfl⟩
  have hc : Nat.card q.range=4 := by
    rw [hr]
    exact SourceCoreProduct.closure_image_card d h e hseed hn hU g hK a hi
  have hVK : D.V.subgroupOf J=pCore 2 J := by
    rw [←hS]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hk : q.ker=D.Vplus.subgroupOf D.UH := by
    ext u
    change f (inclusion hUK u)=1↔u.val∈D.Vplus
    rw [←MonoidHom.mem_ker,restrictedActor_ker_eq_twoCore d hK a hi e,←hVK]
    change u.val∈D.V↔u.val∈D.Vplus
    exact ⟨fun hv => (SourceSecondLayer.seed_intersection d h hU).le ⟨hv,u.property⟩,
      fun hv => h.plus_le hv⟩
  have hker : Nat.card q.ker=8 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe
      (show D.Vplus≤D.UH from le_conjugateSpanBy _ _)).toEquiv,d.seed_card]
  have hh := q.ker.card_mul_index
  rw [index_ker,hker,hc] at hh
  exact hh.symm

theorem seed_centralizer (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val≤D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    D.Vplus⊓centralizer (D.UH:Set G)=D.V₁ := by
  let C := D.Vplus⊓centralizer (D.UH:Set G)
  have hp : D.V₁≤C := le_inf h.point_lt.le
    (le_centralizer_iff.mp (h.UH_le_H.trans h.H_centralizes))
  have hN : D.L₁⊔D.T≤normalizer (C:Set G) :=
    (le_inf h.local_normalizes
      ((h.local_le.trans (le_normalizer_conjugateSpanBy D.Vplus D.H)).trans
        (normalizer_le_normalizer_centralizer D.UH))).trans inf_normalizer_le_normalizer_inf
  rcases h.irreducible C hp inf_le_left hN with he|he
  · exact he
  · exfalso
    have hbot : (D.UH.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)=⊥ := by
      apply bot_unique
      rintro _ ⟨u,hu,rfl⟩
      apply actor_eq_one_of_seed_centralizer d e g hK a hi u
      intro v hv
      exact ((he.symm ▸ hv : v∈C).2 u.val hu).symm
    have hc := SourceCoreProduct.closure_image_card d h e hseed hn hU g hK a hi
    rw [hbot,card_bot] at hc
    contradiction

theorem closure_center (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val≤D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V) :
    center D.UH=D.V₁.subgroupOf D.UH := by
  have hUK : D.UH≤NormalBranch.K D g.val := le_sup_left
  have hVK : pCore 2 (NormalBranch.K D g.val)=D.V.subgroupOf (NormalBranch.K D g.val) := by
    rw [←hS]
    exact (comap_map_eq_self_of_injective (NormalBranch.K D g.val).subtype_injective _).symm
  apply le_antisymm
  · intro u hu
    have hc : u.val∈centralizer (D.Vplus:Set G) := by
      intro v hv
      exact congrArg Subtype.val (mem_center_iff.mp hu ⟨v,le_conjugateSpanBy _ _ hv⟩)
    have hz := actor_eq_one_of_seed_centralizer d e g hK a hi (inclusion hUK u) hc
    have hv : u.val∈D.V := by
      have hm : inclusion hUK u∈(restrictedActor d hK a hi).ker := hz
      rw [restrictedActor_ker_eq_twoCore d hK a hi e,hVK] at hm
      exact hm
    have hs : u.val∈D.Vplus := (SourceSecondLayer.seed_intersection d h hU).le ⟨hv,u.property⟩
    exact (seed_centralizer d h e hseed hn hU g hK a hi).le
      ⟨hs,fun x hx => congrArg Subtype.val (mem_center_iff.mp hu ⟨x,hx⟩)⟩
  · intro u hu
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext ((h.H_centralizes (h.UH_le_H x.property) u.val hu).symm)


theorem local_core_eq_closure (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val≤D.L) (hL : D.L₁≤NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V) : D.L₁.pCoreIn 2=D.UH := by
  let J := NormalBranch.K D g.val
  let f := restrictedActor d hK a hi
  let U := (D.UH.subgroupOf J).map f
  let R := ((D.L₁.pCoreIn 2).subgroupOf J).map f
  have hUK := (closure_reduction h hseed hn).2.1
  have hUp : IsPGroup 2 U :=
    ((show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup).comap_subtype).map f
  have hRp : IsPGroup 2 R := (isPGroup_pCoreIn 2 D.L₁).comap_subtype.map f
  have hc : Nat.card U=4 := SourceCoreProduct.closure_image_card d h e hseed hn hU g hK a hi
  have hidx : U.index=15 := by
    have hh := U.card_mul_index
    rw [hc,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  let P : Sylow 2 (alternatingGroup (Fin 5)) := hUp.toSylow (by rw [hidx];decide)
  have hiR : U≤R := map_mono (subgroupOf_mono J hUK)
  have heR : R=U := P.is_maximal' hRp hiR
  have hVK : pCore 2 J=D.V.subgroupOf J := by
    rw [←hS]
    exact (comap_map_eq_self_of_injective J.subtype_injective _).symm
  have hindex : D.Vplus.relIndex D.V=2 := by
    have hh := (D.Vplus.subgroupOf D.V).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe h.plus_le).toEquiv,d.seed_card,ReturningPlane.module_card d] at hh
    change (D.Vplus.subgroupOf D.V).index=2
    omega
  have hVQ := LocalGeometry.seed_eq_intersection_core h hindex hU
  have hcoreQ : D.L₁.pCoreIn 2≤D.QH := (local_core_intersection h hn).symm.le.trans inf_le_right
  apply le_antisymm ?_ hUK
  intro x hx
  let xJ : J := ⟨x,((pCoreIn_le 2 D.L₁).trans hL) hx⟩
  have hxf : f xJ∈U := heR ▸ mem_map_of_mem f hx
  obtain ⟨u,hu,he⟩ := hxf
  have hk : xJ*u⁻¹∈f.ker := by
    change f (xJ*u⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  rw [restrictedActor_ker_eq_twoCore d hK a hi e,hVK] at hk
  have hr : x*u.val⁻¹∈D.L₁.pCoreIn 2 :=
    (D.L₁.pCoreIn 2).mul_mem hx ((D.L₁.pCoreIn 2).inv_mem (hUK hu))
  have hplus : x*u.val⁻¹∈D.Vplus := hVQ.le ⟨hk,hcoreQ hr⟩
  have hh := D.UH.mul_mem (le_conjugateSpanBy _ _ hplus) hu
  change x*u.val⁻¹*u.val∈D.UH at hh
  simpa only [inv_mul_cancel_right] using hh

theorem closure_extraspecial (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val≤D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V) : IsExtraspecial 2 D.UH := by
  let : Fact (IsPGroup 2 D.UH) := ⟨h.g2_hypothesis.U_isPGroup⟩
  have hZ := closure_center d h e hseed hn hU g hK a hi hS
  have hpoint : D.V₁≤D.UH := h.point_lt.le.trans (le_conjugateSpanBy _ _)
  have hZcard : Nat.card (center D.UH)=2 := by
    rw [hZ,Nat.card_congr (subgroupOfEquivOfLe hpoint).toEquiv,h.point_card]
  have hphi : frattini D.UH≤center D.UH := by
    rw [hZ]
    intro u hu
    exact h.frattini_UH_le_point (mem_map_of_mem D.UH.subtype hu)
  refine ⟨hZcard,?_,?_⟩
  · refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N:=center D.UH)).mpr
        ((commutator_le_frattini_of_isPGroup (p:=2)).trans hphi)
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro q
      induction q using QuotientGroup.induction_on with
      | H u =>
        exact (QuotientGroup.eq_one_iff (N:=center D.UH) (u^2)).mpr
          (hphi (pth_power_mem_frattini_of_isPGroup (p:=2) u))
  · apply QuotientGroup.nontrivial_iff.mpr
    intro he
    have hc : Nat.card (center D.UH)=Nat.card D.UH := by rw [he,Nat.card_congr topEquiv.toEquiv]
    rw [hZcard,closure_card d h e hseed hn hU g hK a hi hS] at hc
    contradiction

theorem closure_quaternion (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val≤D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V) :
    Nonempty (QuaternionCentralProductData D.UH) := by
  let := closure_extraspecial d h e hseed hn hU g hK a hi hS
  let E := D.Vplus.subgroupOf D.UH
  have hVU : D.Vplus≤D.UH := le_conjugateSpanBy _ _
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hVU).mpr
    ((h.UH_le_QH.trans h.QH_le_T).trans (le_sup_right.trans h.local_normalizes))
  let := h.elementary
  let : IsElementaryAbelian 2 D.Vplus := IsElementaryAbelian.of_le h.plus_le
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVU
  have hE : Nat.card E=8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans d.seed_card
  have hZE : center D.UH≤E := by
    rw [closure_center d h e hseed hn hU g hK a hi hS]
    exact comap_mono h.point_lt.le
  obtain ⟨B,C,hB,hC,hspan,hmeet,hcomm⟩ :=
    exists_quaternion_factors_of_extraspecial_thirty_two_elementary
      (closure_card d h e hseed hn hU g hK a hi hS) E hE hZE
  exact ⟨⟨B,C,hB,hC,hmeet,hcomm,hspan⟩⟩

include d in
/-- Clause13.5.15(5), with actual quaternion factors and the original centre. -/
theorem source13_5_15_five (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) :
    D.L₁.pCoreIn 2=D.UH ∧ Nat.card D.UH=32 ∧
      center D.UH=D.V₁.subgroupOf D.UH ∧
      Nonempty (D.UH≃*QuaternionCentralProduct.Model) ∧
      ∃q:QuaternionCentralProductData D.UH,
        (q.left⊓q.right).map D.UH.subtype=D.V₁ := by
  obtain ⟨a,g,_,_,hK,hL,_,_,_,hi,hS⟩ :=
    SourceCoreCollapse.exists_original_collapsed_pair d h e hseed hn hU
  have hZ := closure_center d h e hseed hn hU g hK a hi hS
  obtain ⟨q⟩ := closure_quaternion d h e hseed hn hU g hK a hi hS
  refine ⟨local_core_eq_closure d h e hseed hn hU g hK hL a hi hS,
    closure_card d h e hseed hn hU g hK a hi hS,hZ,q.nonempty_model_equiv,q,?_⟩
  rw [←q.center_eq,hZ,map_subgroupOf_eq_of_le
    (show D.V₁≤D.UH from h.point_lt.le.trans (le_conjugateSpanBy _ _))]

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceQuaternion
end
