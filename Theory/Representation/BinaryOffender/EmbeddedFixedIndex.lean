module
public import Theory.Representation.NormalElementaryQuotient.FixedIndex

/-!
# Centralizer indices for an embedded binary representation

An injective multiplicative embedding identifies the full binary module and
its fixed space with the actual subgroup and its centralizer. Counting both
spaces identifies the literal centralizer index with the power of two given
by fixed codimension. The ambient group need not be finite.

Source application: MS93 (3.3), printed p.867, where the whole X-layer and
the critical root retain their original embeddings.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G D V : Type*} [Group G] [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem embedded_centralizer_index (σ : Representation (ZMod 2) D V)
    (X A : Subgroup G) (j : Multiplicative V →* G) (hj : Function.Injective j)
    (hjr : j.range = X) (β : A →* D)
    (hβ : ∀ (a : A) (v : V),
      j (Multiplicative.ofAdd (σ (β a) v)) =
        (a : G) * j (Multiplicative.ofAdd v) * (a : G)⁻¹) :
    (centralizer (A : Set G)).relIndex X = 2 ^ fixedCodim σ β.range := by
  let d : Multiplicative V ≃* X :=
    (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hjr)
  have hfix (v : V) : v ∈ fixedSpace σ β.range ↔
      j (Multiplicative.ofAdd v) ∈ centralizer (A : Set G) := by
    constructor
    · intro hv a ha
      have he := hβ ⟨a,ha⟩ v
      have hf : σ (β ⟨a,ha⟩) v = v := hv ⟨β ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩
      rw [hf] at he
      exact mul_inv_eq_iff_eq_mul.mp he.symm
    · intro hv a
      obtain ⟨b,hb⟩ := a.property
      change σ a.val v = v
      rw [←hb]
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hβ,hv b b.property,mul_inv_cancel_right]
  let ef : fixedSpace σ β.range ≃ (X ⊓ centralizer (A : Set G) : Subgroup G) :=
    { toFun v := ⟨j (Multiplicative.ofAdd v.val),hjr ▸ ⟨Multiplicative.ofAdd v.val,rfl⟩,
        (hfix v.val).mp v.property⟩
      invFun x := ⟨(d.symm ⟨x.val,x.property.1⟩).toAdd, by
        apply (hfix _).mpr
        have he : j (d.symm ⟨x.val,x.property.1⟩) = x.val :=
          congrArg Subtype.val (d.apply_symm_apply ⟨x.val,x.property.1⟩)
        change j (d.symm ⟨x.val,x.property.1⟩) ∈ _
        rw [he]
        exact x.property.2⟩
      left_inv v := by
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd (d.symm_apply_apply (Multiplicative.ofAdd v.val))
      right_inv x := by
        apply Subtype.ext
        exact congrArg (fun y : X => (y : G)) (d.apply_symm_apply ⟨x.val,x.property.1⟩) }
  have hc : Nat.card (X ⊓ centralizer (A : Set G) : Subgroup G) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace σ β.range) := by
    rw [←Nat.card_congr ef]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := fixedSpace σ β.range)
  have hX : Nat.card X = 2 ^ Module.finrank (ZMod 2) V := by
    rw [←Nat.card_congr d.toEquiv]
    change Nat.card V = _
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G)
    (X ⊓ centralizer (A : Set G)) X bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hc,hX,
    ←fixedCodim_add_finrank σ β.range,pow_add] at hh
  exact Nat.eq_of_mul_eq_mul_left (n := 2 ^ Module.finrank (ZMod 2) (fixedSpace σ β.range))
    (by positivity) (by simpa only [mul_comm] using hh)
end Representation.BinaryOffender
