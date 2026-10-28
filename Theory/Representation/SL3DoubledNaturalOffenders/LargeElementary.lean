module
public import Theory.Representation.SL3DoubledNaturalOffenders.AllFields
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.EndFieldTransfer
public import Theory.ElementaryAbelian.Injective

/-!
# Large elementary subgroups over a doubled natural core

Let Q be a self-centralizing normal elementary two-subgroup, contained in
an invariant subgroup K whose action on Q is two copies of the natural
SL₃ module over a field of order 2ⁿ, n>1. An elementary subgroup A with
|Q|≤|A| induces an offender on Q unless it centralizes Q. The full binary
normalizer estimate places that offender in the actual SL₃ image; the
kernel Q≤K then lifts this containment to A≤K.

The argument retains the full special linear group, including its cubic
center and field four. The original crossed-core application is in
NonblockMSDoubledCrossing. Source: Aschbacher--Smith C.1.36(2), printed
p.140, and B.5.9--10, pp.107--109.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Representation.SL3DoubledNaturalOffenders
open BinaryOffender NormalElementaryQuotient
variable {G F : Type*} [Group G] [Field F] [Finite F]
  [Algebra (ZMod 2) F]

/-- An elementary subgroup at least as large as a self-centralizing doubled
natural core lies in the original component. -/
theorem large_elementary_le_component
    (Q K : Subgroup G) [Q.Normal] [IsElementaryAbelian 2 Q] [K.Normal]
    (hQK : Q ≤ K) (hC : centralizer (Q : Set G) = Q)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (a : K →* SL F) (ha : Function.Surjective a)
    (e : Q ≃* Multiplicative (Space F))
    (he : ∀ (k : K) (u v : Q), (v : G) = k * (u : G) * (k : G)⁻¹ →
      (e v).toAdd = representation F (a k) (e u).toAdd)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hc : Nat.card Q ≤ Nat.card A) :
    A ≤ K := by
  let q := QuotientGroup.mk' Q
  have hker : q.ker = centralizer (Q : Set G) := (QuotientGroup.ker_mk' Q).trans hC.symm
  let ρ := NormalElementaryQuotient.representation Q q (QuotientGroup.mk'_surjective Q) hker
  let E : Additive Q ≃ₗ[ZMod 2] Space F :=
    { e.toAdditiveLeft with map_smul' := ZMod.map_smul e.toAdditiveLeft }
  let τ : Representation (ZMod 2) (G ⧸ Q) (Space F) := E.conjRingEquiv.toMonoidHom.comp ρ
  let f := τ.asGroupHom
  have hf : Function.Injective f := by
    intro x y hxy
    exact E.conjRingEquiv.injective.comp
      (NormalElementaryQuotient.representation_injective Q q (QuotientGroup.mk'_surjective Q) hker)
      (congrArg Units.val hxy)
  have hact (k : K) (v : Additive Q) : E (ρ (q k) v) = representation F (a k) (E v) :=
    he k v.toMul (ρ (q k) v).toMul
      (NormalElementaryQuotient.representation_apply Q q (QuotientGroup.mk'_surjective Q) hker k v)
  have hk (k : K) : f (q k) = (representation F).asGroupHom (a k) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change E (ρ (q k) (E.symm v)) = _
    rw [hact,E.apply_symm_apply]
    rfl
  let j := f.comp q
  have hK : K.map j = component F := by
    apply le_antisymm
    · rintro _ ⟨k,hk',rfl⟩
      exact ⟨a ⟨k,hk'⟩,(hk ⟨k,hk'⟩).symm⟩
    · rintro _ ⟨g,rfl⟩
      obtain ⟨k,rfl⟩ := ha g
      exact ⟨k,k.property,hk k⟩
  have hjker : j.ker = Q := by
    ext g
    change f (q g) = 1 ↔ g ∈ Q
    rw [←map_one f,hf.eq_iff]
    exact QuotientGroup.eq_one_iff g
  have hAN : A.map j ≤ normalizer F := by
    change A.map j ≤ Subgroup.normalizer (component F)
    rw [←hK]
    exact (map_mono (show A ≤ Subgroup.normalizer K by
      rw [Subgroup.normalizer_eq_top]; exact le_top)).trans (K.le_normalizer_map j)
  have himage : A.map j ≤ component F := by
    by_cases hzero : A.map j = ⊥
    · rw [hzero]; exact bot_le
    let : Finite (Module.End (ZMod 2) (Space F)) :=
      Finite.of_injective (fun b : Module.End (ZMod 2) (Space F) => (b : Space F → Space F))
        DFunLike.coe_injective
    let : IsElementaryAbelian 2 (A.map j) := IsElementaryAbelian.map j
    have hE : IsElementaryTwo (A.map j) := ⟨hzero,inferInstance⟩
    have hfixed : Nat.card (Q ⊓ A : Subgroup G) ≤ Nat.card (fixedSpace (action F) (A.map j)) := by
      let i : (Q ⊓ A : Subgroup G) → fixedSpace (action F) (A.map j) := fun v =>
        ⟨(e ⟨v,v.property.1⟩).toAdd,by
          intro b
          obtain ⟨x,hx,hxb⟩ := b.property
          change action F b.val _ = _
          rw [←hxb]
          change E (ρ (q x) (E.symm (E (Additive.ofMul ⟨v,v.property.1⟩)))) = _
          rw [E.symm_apply_apply]
          apply congrArg E
          apply Additive.toMul.injective
          apply Subtype.ext
          change ((ρ (q x) (Additive.ofMul ⟨v,v.property.1⟩)).toMul : G) = v
          rw [NormalElementaryQuotient.representation_apply]
          have hcomm : x * (v : G) = (v : G) * x := congrArg Subtype.val
            (mul_comm (⟨x,hx⟩ : A) ⟨v,v.property.2⟩)
          change x * (v : G) * x⁻¹ = (v : G)
          rw [hcomm,mul_inv_cancel_right]⟩
      apply Nat.card_le_card_of_injective i
      intro u v huv
      exact Subtype.ext (congrArg (fun w : Q => (w : G))
        (e.injective (Multiplicative.toAdd.injective (congrArg Subtype.val huv))))
    have hcard : Nat.card (Q ⊓ A : Subgroup G) * Nat.card (A.map j) = Nat.card A := by
      have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (j.ker ⊓ A) A bot_le inf_le_right
      rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,relIndex_ker] at hh
      simpa only [hjker] using hh
    have ho : IsOffender (action F) (A.map j) := by
      apply (EndFieldTransfer.offender_iff_card (action F) _ hE).mpr
      calc
        Nat.card (Space F) = Nat.card Q := (Nat.card_congr e.toEquiv).symm
        _ ≤ Nat.card A := hc
        _ = Nat.card (A.map j) * Nat.card (Q ⊓ A : Subgroup G) := by rw [←hcard,mul_comm]
        _ ≤ Nat.card (A.map j) * Nat.card (fixedSpace (action F) (A.map j)) :=
          Nat.mul_le_mul_left _ hfixed
    exact AllFields.offender_le_component_of_le_normalizer hn hF ho hAN
  rw [←hK] at himage
  intro x hx
  obtain ⟨k,hk,hkx⟩ := himage (mem_map_of_mem j hx)
  have hdiff : k⁻¹*x ∈ Q := by
    rw [←hjker]
    change j (k⁻¹*x) = 1
    rw [map_mul,map_inv,hkx,inv_mul_cancel]
  simpa only [mul_inv_cancel_left] using K.mul_mem hk (hQK hdiff)
end Representation.SL3DoubledNaturalOffenders
