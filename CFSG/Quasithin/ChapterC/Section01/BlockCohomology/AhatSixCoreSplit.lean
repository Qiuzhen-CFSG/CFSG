module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Ahat6Centralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import Theory.Representation.FirstCohomologyAutomorphism.Subkernel
public import Theory.Representation.CentralFixedPointCohomology

/-!
# The full two-core split for an exceptional triple-six block

The actual central cubic acts without fixed vectors on the entire block
module. Its quadratic relation kills first cohomology, so every automorphism
fixing that module and inducing the identity modulo the two-core is inner
by an element of the module. This yields the literal two-core factorization
for a normalizing overgroup, retaining any central factor of the two-core.

Source: Aschbacher--Smith C.1.13(b,c), I.1.6(9) and12.7.6(1),
printed pp.124--125 and840.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
variable {L : Type*} [Group L]

private theorem ahatSix_H1_subsingleton (h : IsExceptionalAhat6Block L) :
    letI := h.1.elementary
    Subsingleton (OneCohomology.H1 (uRepresentation h.1)) := by
  let := h.1.finite
  let := h.1.elementary
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (L ⧸ pCore 2 L)) 3
    (by rw [h.2.2.1])
  have hne : (z : L ⧸ pCore 2 L) ≠ 1 := by
    intro he
    have he' : z = 1 := Subtype.ext he
    rw [he',orderOf_one] at hz
    contradiction
  have hz3 : (z : L ⧸ pCore 2 L) ^ 3 = 1 :=
    congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)
  let ρ := uRepresentation h.1
  have hq := central_cubic_quadratic h z z.property hne hz3
  have hf (v : Additive (blockU L)) (hv : ρ z v = v) : v = 0 := by
    have he := LinearMap.congr_fun hq v
    change ρ z (ρ z v) + ρ z v + v = 0 at he
    rw [hv,hv] at he
    have h2 : v+v=0 := by
      calc
        v+v = (2 : ZMod 2) • v := (two_smul (ZMod 2) v).symm
        _ = 0 := by rw [show (2 : ZMod 2)=0 by decide,zero_smul]
    simpa only [h2,zero_add] using he
  let τ : Additive (blockU L) →ₗ[ZMod 2] Additive (blockU L) := ρ z - 1
  have hi : Function.Injective τ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro v hv
    exact hf v (sub_eq_zero.mp hv)
  exact OneCohomology.subsingleton_H1_of_central_fixedPointFree ρ z z.property hf
    (LinearMap.surjective_of_injective hi)

/-- Core-trivial automorphisms fixing the full original module are inner
by that module; no equality between the module and the two-core is assumed. -/
theorem IsExceptionalAhat6Block.automorphism_inner_of_core_displacement
    (h : IsExceptionalAhat6Block L) (α : MulAut L)
    (hd : ∀ x, α x * x⁻¹ ∈ pCore 2 L)
    (hfix : ∀ u ∈ blockU L, α u = u) :
    ∃ u : blockU L, ∀ x, α x = (u : L)⁻¹ * x * u := by
  let := h.1.finite
  let := h.1.elementary
  have hdU (x : L) : α x * x⁻¹ ∈ blockU L := by
    have he := DFunLike.congr_fun (h.1.quotient_blockU_aut_eq_one α hd)
      (QuotientGroup.mk' (blockU L) x)
    rw [quotientAut_apply_mk] at he
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  have hz : blockU L ⊓ center L = ⊥ := by
    apply le_bot_iff.mp
    rintro x ⟨hx,hxc⟩
    exact congrArg Subtype.val (h.fixed_coreCenter_eq_one ⟨x,hx⟩ (by
      intro y _
      exact mem_center_iff.mp hxc y))
  have hcore := OneCohomology.automorphism_fixes_centralizing_layer
    (blockU L) (pCore 2 L) h.1.core_centralizes_blockU le_rfl hz α hdU hfix
  let ρ := uRepresentation h.1
  let f := QuotientGroup.mk' (pCore 2 L)
  let e : blockU L ≃* Multiplicative (Additive (blockU L)) := MulEquiv.refl _
  let : Subsingleton (OneCohomology.H1 ρ) := ahatSix_H1_subsingleton h
  apply OneCohomology.automorphism_inner_of_H1_zero_of_subkernel
    (blockU L) f (QuotientGroup.mk'_surjective _) e ρ (fun g v => ?_)
    α hdU (by simpa only [f,QuotientGroup.ker_mk'] using hcore)
  exact uRepresentation_apply h.1 g v

variable {G : Type*} [Group G] [Finite G]

theorem IsExceptionalAhat6Block.two_subgroup_eq_module_sup_centralizer
    {K P : Subgroup G} (hK : IsExceptionalAhat6Block K)
    (hP : IsPGroup 2 P) (hKP : K ≤ normalizer (P : Set G))
    (hUP : (blockU K).map K.subtype ≤ P)
    (hc : ⁅K,P⁆ ≤ K.pCoreIn 2) :
    P = (blockU K).map K.subtype ⊔ (P ⊓ Subgroup.centralizer (K : Set G)) := by
  have hPK : P ≤ normalizer (K : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      ((commutator_comm P K).le.trans (hc.trans (pCoreIn_le 2 K)))
  have hPU := hK.1.normalizing_twoGroup_centralizes_blockU hP hKP hPK
  apply le_antisymm
  · intro p hp
    let α := K.normalizerMonoidHom ⟨p,hPK hp⟩
    have hd (x : K) : α x * x⁻¹ ∈ pCore 2 K := by
      have hx := hc ((commutator_comm P K).le (commutator_mem_commutator hp x.property))
      obtain ⟨z,hz,he⟩ := hx
      exact (Subtype.ext he : z = α x * x⁻¹) ▸ hz
    have hf (u : K) (hu : u ∈ blockU K) : α u = u := by
      apply Subtype.ext
      change p * (u : G) * p⁻¹ = (u : G)
      rw [←hPU hp u (mem_map_of_mem K.subtype hu),mul_inv_cancel_right]
    obtain ⟨u,hu⟩ := hK.automorphism_inner_of_core_displacement α hd hf
    have huG : ((u : K) : G) ∈ (blockU K).map K.subtype := mem_map_of_mem K.subtype u.property
    have hcG : ((u : K) : G) * p ∈ Subgroup.centralizer (K : Set G) := by
      intro k hk
      have he := congrArg (fun z : K => (z : G)) (hu ⟨k,hk⟩)
      change p*k*p⁻¹ = ((u : K) : G)⁻¹*k*u at he
      calc
        k * (((u : K) : G)*p) = u * (((u : K) : G)⁻¹*k*u) * p := by group
        _ = u * (p*k*p⁻¹) * p := by rw [←he]
        _ = (((u : K) : G)*p)*k := by group
    have hm := mul_mem_sup ((blockU K).map K.subtype |>.inv_mem huG)
      (show ((u : K) : G)*p ∈ P ⊓ Subgroup.centralizer (K : Set G) from
        ⟨P.mul_mem (hUP huG) hp,hcG⟩)
    simpa only [inv_mul_cancel_left] using hm
  · exact sup_le hUP inf_le_left

end CFSG.Quasithin.ChapterC

namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem IsExceptionalAhat6Block.normalizer_twoCore_eq_module_sup_centralizer
    {K H : Subgroup G} (hK : IsExceptionalAhat6Block K)
    (hKH : K ≤ H) (hH : H ≤ normalizer (K : Set G)) :
    H.pCoreIn 2 = (blockU K).map K.subtype ⊔
      (H.pCoreIn 2 ⊓ Subgroup.centralizer (K : Set G)) := by
  let Q := H.pCoreIn 2
  have hQN : Q ≤ normalizer (K : Set G) := (pCoreIn_le 2 H).trans hH
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hKQ := hKH.trans hHQ
  have hU : (blockU K).map K.subtype ≤ Q := by
    apply le_pCoreIn_of_normalizes
      ((pCore_isPGroup.to_le blockU_le_core).map K.subtype)
      ((map_subtype_le _).trans hKH)
    exact hH.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hc : ⁅K,Q⁆ ≤ K.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 H).to_le
        (le_normalizer_iff_commutator_le_right.mp hKQ))
      (le_normalizer_iff_commutator_le_left.mp hQN)
      (normalizer_commutator_ge_left K Q)
  exact hK.two_subgroup_eq_module_sup_centralizer (isPGroup_pCoreIn 2 H) hKQ hU hc

end CFSG.Quasithin.ChapterC
