module
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryConjugationSection

/-!
# Literal conjugation coordinates for a normal elementary subgroup

For V ≤ H normalized by H, descend conjugation to H/C_H(V). The resulting
binary representation is faithful on the additive copy of V inside H,
and its trivial-denominator section sends each vector to its original
group element. Neither the centralizer nor its quotient is replaced by
a two-core or a group-family label.

This extends the normal elementary quotient construction with the exact
`BinaryConjugationSection` coordinates. The enlarged replacement-section
application in DGS 6.4 uses it for H=L_lambda, preserving normality of the
selected section kernel in the full enlarged endpoint.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G]

/-- The centralizer quotient acts faithfully with literal trivial-denominator conjugation coordinates. -/
theorem exists_faithful_quotient_action (H V : Subgroup G)
    (hVH : V ≤ H) (hn : H ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 V] :
    ∃ hE : IsElementaryAbelian 2 (V.subgroupOf H),
      letI := hE
      ∃ (K : Subgroup H) (hK : K.Normal),
        letI := hK
        ∃ σ : Representation (ZMod 2) (H ⧸ K) (Additive (V.subgroupOf H)),
          K = (centralizer (V : Set G)).subgroupOf H ∧ Function.Injective σ ∧
            Nonempty (BinaryConjugationSection H V ⊥ (σ.comp (QuotientGroup.mk' K))) := by
  let N := V.subgroupOf H
  let hE : IsElementaryAbelian 2 N := IsElementaryAbelian.subgroupOf hVH
  let := hE
  refine ⟨hE,?_⟩
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hVH).mpr hn
  let K := centralizer (N : Set H)
  let hK : K.Normal := inferInstance
  let := hK
  let q := QuotientGroup.mk' K
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hk : q.ker = centralizer (N : Set H) := QuotientGroup.ker_mk' K
  let σ := NormalElementaryQuotient.representation N q hq hk
  refine ⟨K,hK,σ,?_,NormalElementaryQuotient.representation_injective N q hq hk,?_⟩
  · ext x
    constructor
    · intro hx v hv
      have he := hx ⟨v,hVH hv⟩ hv
      exact congrArg Subtype.val he
    · intro hx v hv
      apply Subtype.ext
      exact hx v hv
  · let e : N ≃* V := subgroupOfEquivOfLe hVH
    refine ⟨{
      section_le := hVH
      kernel_le := bot_le
      normalized := hn
      coordinates := {
        toFun := fun v => Multiplicative.ofAdd (Additive.ofMul (e.symm v))
        map_one' := by simp only [map_one]; rfl
        map_mul' := fun _ _ => by simp only [map_mul]; rfl }
      onto := ?_
      kernel_eq := ?_
      equivariant := ?_ }⟩
    · intro w
      exact ⟨e w.toAdd.toMul,congrArg (fun v => Multiplicative.ofAdd (Additive.ofMul v))
        (e.symm_apply_apply _)⟩
    · ext v
      change e.symm v = 1 ↔ (v : G) = 1
      constructor
      · intro hv
        have he := congrArg e hv
        rw [e.apply_symm_apply,map_one] at he
        exact congrArg Subtype.val he
      · intro hv
        have he : v = 1 := Subtype.ext hv
        rw [he,map_one]
    · intro x v
      apply Multiplicative.toAdd.injective
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      exact (congrArg Subtype.val
        (NormalElementaryQuotient.representation_apply N q hq hk x
          (Additive.ofMul (e.symm v)))).symm
end Representation.BinaryConjugationSection
