module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Normal kernels in a quasisimple two-group extension

For a normal C-component K with quasisimple two-core quotient and a
two-group supplement, the image of K is the full generalized Fitting
subgroup modulo O₂. A normal kernel containing O₂ but not K therefore
lies in the center of that image. This gives the literal upper bound by
O₂ times the preimage of Z(K/O₂K).

The quotient is again two-core-free. Otherwise the preimage of its two-core
would be an abelian normal subgroup of the original core-free quotient;
its Sylow two-subgroup is trivial, so its two-group image is trivial too.
No action on a module, seed, or kernel-bound hypothesis is used here.

Source: Aschbacher--Smith C.2.7(1), printed pp.145–146, the group-theoretic
part of the B.2.10 reduction.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory.QuasisimpleKernel
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite H] in
private theorem normal_commutative_pgroup_image_trivial
    (hcore : pCore 2 G = ⊥) (P : Subgroup G) [P.Normal] [IsMulCommutative P]
    (f : P →* H) (hp : IsPGroup 2 H) : f = 1 := by
  let S : Sylow 2 P := Classical.choice inferInstance
  have hS : (S : Subgroup P) ≤ pCore 2 P := le_sSup ⟨inferInstance,S.isPGroup'⟩
  have hPG : (pCore 2 P).map P.subtype ≤ pCore 2 G :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map P.subtype⟩
  have hbot : (S : Subgroup P) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp
    exact le_bot_iff.mp ((map_mono hS).trans (hPG.trans hcore.le))
  have hres : pResidual 2 P ≤ f.ker := sInf_le ⟨inferInstance,
    (hp.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm⟩
  have ht : pResidual 2 P = ⊤ := by
    simpa only [hbot,sup_bot_eq] using pResidual_sup_sylow_eq_top S
  apply MonoidHom.ext
  intro x
  exact hres (ht ▸ mem_top x)

/-- A normal subgroup avoiding the quasisimple F* lies in its center. -/
private theorem normal_le_component_center
    (K N : Subgroup G) [K.Normal] [N.Normal] [IsQuasisimple K]
    (hF : generalizedFitting G = K) (hne : ¬ K ≤ N) :
    N ≤ (center K).map K.subtype := by
  have hc := (show IsComponent G K from ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩).normal_dichotomy N
  have hNC : N ≤ centralizer (K : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hc.resolve_left hne))
  have hNK : N ≤ K := hNC.trans (hF ▸ centralizer_generalizedFitting_le G)
  intro n hn
  refine ⟨⟨n,hNK hn⟩,?_,rfl⟩
  exact mem_center_iff.mpr fun k => Subtype.ext (hNC hn k k.property)

/-- Quotients preserving the quasisimple component stay two-core-free. -/
private theorem quotient_core_eq_bot_of_component_survives
    (K N : Subgroup G) [K.Normal] [N.Normal] [IsQuasisimple K]
    (hF : generalizedFitting G = K) (hcore : pCore 2 G = ⊥)
    (hne : ¬ K ≤ N) : pCore 2 (G ⧸ N) = ⊥ := by
  let q := QuotientGroup.mk' N
  let P := (pCore 2 (G ⧸ N)).comap q
  let : P.Normal := inferInstance
  have hKP : ¬ K ≤ P := by
    intro h
    let f : K →* pCore 2 (G ⧸ N) := (q.comp K.subtype).codRestrict _ (fun k => h k.property)
    have hperfect : IsPPerfect 2 K := by
      intro A hA hp
      let : A.Normal := hA
      let : Group.IsNilpotent (K ⧸ A) := hp.isNilpotent
      exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ A)
    have hf : f = 1 := hperfect.hom_eq_one_of_isPGroup pCore_isPGroup f
    apply hne
    intro k hk
    have he := congrArg (fun x : pCore 2 (G ⧸ N) => (x : G ⧸ N)) (DFunLike.congr_fun hf ⟨k,hk⟩)
    exact (QuotientGroup.eq_one_iff k).mp he
  have hPZ := normal_le_component_center K P hF hKP
  let : IsMulCommutative P := isMulCommutative_iff.mpr fun a b =>
    (inclusion_injective hPZ) (by simp only [map_mul]; exact mul_comm _ _)
  let f : P →* pCore 2 (G ⧸ N) := (q.comp P.subtype).codRestrict _ (fun x => x.property)
  have hf : f = 1 := normal_commutative_pgroup_image_trivial hcore P f pCore_isPGroup
  apply bot_unique
  intro x hx
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
  exact congrArg (fun a : pCore 2 (G ⧸ N) => (a : G ⧸ N))
    (DFunLike.congr_fun hf ⟨g,hx⟩)

/-- The normal kernel upper bound and reducedness before a module is chosen. -/
theorem normal_kernel_structure
    (K S N : Subgroup G) [K.Normal] [N.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤)
    (hQN : pCore 2 G ≤ N) (hKN : ¬ K ≤ N) :
    N ≤ pCore 2 G ⊔ ((center (K ⧸ pCore 2 K)).comap
      (QuotientGroup.mk' (pCore 2 K))).map K.subtype ∧
    pCore 2 (G ⧸ N) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  let B := K.map q
  let C := N.map q
  let : B.Normal := Normal.map inferInstance q hq
  let : C.Normal := Normal.map inferInstance q hq
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hquot : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (S.map q) (hS.map q) (by
      rw [← Subgroup.map_sup,hgen,map_top_of_surjective q hq])
  have hF : generalizedFitting (G ⧸ pCore 2 G) = B :=
    generalizedFitting_eq_of_quasisimple_two_quotient B hquot (pCore_quotient_pCore_eq_bot 2)
  have hBC : ¬ B ≤ C := by
    intro hh
    apply hKN
    have ht := map_le_iff_le_comap.mp hh
    rwa [comap_map_eq_self (show q.ker ≤ N by rwa [QuotientGroup.ker_mk'])] at ht
  have hCZ := normal_le_component_center B C hF hBC
  have hred := quotient_core_eq_bot_of_component_survives B C hF
    (pCore_quotient_pCore_eq_bot 2) hBC
  refine ⟨?_,?_⟩
  · intro x hx
    obtain ⟨b,hbz,hbx⟩ := hCZ (mem_map_of_mem q hx)
    obtain ⟨k,hk,hkb⟩ := b.property
    have hke : q k = q x := hkb.trans hbx
    have hkZ : (⟨k,hk⟩ : K) ∈ (center (K ⧸ pCore 2 K)).comap (QuotientGroup.mk' (pCore 2 K)) := by
      apply mem_center_iff.mpr
      intro a
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) a
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← map_commutatorElement]
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [pCore_subnormal_eq_comap 2 hK.subnormal]
      change ((a : G) * k * (a : G)⁻¹ * k⁻¹) ∈ pCore 2 G
      apply (QuotientGroup.eq_one_iff (N := pCore 2 G) _).mp
      change q ((a : G) * k * (a : G)⁻¹ * k⁻¹) = 1
      rw [map_mul,map_mul,map_mul,map_inv,map_inv]
      have hh := congrArg Subtype.val (mem_center_iff.mp hbz ⟨q a,mem_map_of_mem q a.property⟩)
      change q a * (b : G ⧸ pCore 2 G) = (b : G ⧸ pCore 2 G) * q a at hh
      rw [hkb,hh]
      group
    have hdiff : k⁻¹*x ∈ pCore 2 G := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (k⁻¹*x) = 1
      rw [map_mul,map_inv,hke,inv_mul_cancel]
    have hh := (pCore 2 G ⊔ ((center (K ⧸ pCore 2 K)).comap
      (QuotientGroup.mk' (pCore 2 K))).map K.subtype).mul_mem
      (mem_sup_right (mem_map_of_mem K.subtype hkZ)) (mem_sup_left hdiff)
    simpa only [Subgroup.subtype_apply,Subtype.coe_mk,mul_inv_cancel_left] using hh
  · let e := QuotientGroup.quotientQuotientEquivQuotient (pCore 2 G) N hQN
    have he := pCore_map_iso 2 e
    rw [hred,Subgroup.map_bot] at he
    exact he.symm

end Theory.GroupTheory.QuasisimpleKernel
