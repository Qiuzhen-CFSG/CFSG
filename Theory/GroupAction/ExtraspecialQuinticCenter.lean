module
public import Theory.Representation.ExtraspecialQuinticCenter
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Theory.Frattini.PGroup
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupAction.SubgroupConjugation

/-!
# Extraspecial quintic centers acting on two-groups

A faithful action of an extraspecial group of order 125 stays faithful on
the Frattini quotient of a finite two-group. The binary central-action
bound there gives fixed index at least 2^20. An equivariant quotient cannot
increase fixed index, so the bound holds on the original two-group.
The ambient version retains the actual conjugation action and embedded
center, expressing the result as a relative centralizer index.

Source: Aschbacher--Smith, conclusion of 4.3.2, printed p.618. This replaces
chief-series bookkeeping by the same fixed-index inequality and does not
assume any unitary-group or parabolic identification.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace ExtraspecialQuinticCenter

/-- A faithful extraspecial action has central fixed index at least 2^20. -/
theorem fixedIndex_lower_bound
    {P Q : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
    [Group Q] [Finite Q] [MulDistribMulAction P Q] [FaithfulSMul P Q]
    (hP : Nat.card P = 5 ^ 3) (hQ : IsPGroup 2 Q) :
    2 ^ 20 ≤ (FixedPoints.subgroup (center P) Q).index := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let E := Q ⧸ frattini Q
  let : IsElementaryAbelian 2 E := isElementaryAbelian_quotient_frattini (p := 2)
  let : MulDistribMulAction P E :=
    quotientMulDistribMulAction (frattini Q) (isInvariant_of_characteristic (frattini Q))
  let : FaithfulSMul P E := MonoidHom.faithfulSMul_frattini_of_coprime hQ
    (by rw [hP]; decide)
  let ρ : Representation (ZMod 2) P (Additive E) := ofElementaryAbelianAction
  have hf : Function.Injective ρ := by
    intro a b hab
    apply FaithfulSMul.eq_of_smul_eq_smul (α := E)
    intro e
    exact congrArg Additive.toMul (LinearMap.congr_fun hab (Additive.ofMul e))
  have hcenter : ¬ center P ≤ ρ.ker := by
    intro hk
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hf] using hk)
    have hc := IsExtraspecial.center_order_p 5 P
    rw [hb, card_bot] at hc
    omega
  have hl := Representation.ExtraspecialQuinticCenter.center_fixedIndex_lower_bound ρ hP hcenter
  have he : (FixedPoints.subgroup (center P) E).index =
      BinaryFixedPoints.fixedIndex (ρ.comp (center P).subtype) := by
    apply BinaryFixedPoints.fixedIndex_eq_of_equivariant
      (ρ.comp (center P).subtype) (MonoidHom.id _) Function.surjective_id
      (MulEquiv.refl E)
    intro a e
    rfl
  rw [← he] at hl
  exact hl.trans (fixedPoints_index_le_of_surjective_equivariant
    (QuotientGroup.mk' (frattini Q)) (QuotientGroup.mk'_surjective _) (by
      intro a q
      rfl))

/-- The bound for the literal ambient conjugation action, including its kernel. -/
theorem centralizer_relIndex_lower_bound
    {G : Type*} [Group G] [Finite G]
    (P Q : Subgroup G) [IsExtraspecial 5 P]
    (hP : Nat.card P = 5 ^ 3) (hQ : IsPGroup 2 Q)
    (hn : P ≤ normalizer (Q : Set G))
    (hf : P ⊓ centralizer (Q : Set G) = ⊥) :
    2 ^ 20 ≤ (centralizer ((center P).map P.subtype : Set G)).relIndex Q := by
  let := conjMulDistribMulActionOfLeNormalizer P Q hn
  let : FaithfulSMul P Q := by
    constructor
    intro a b hab
    apply Subtype.ext
    have hc : (a : G)⁻¹ * b ∈ centralizer (Q : Set G) := by
      intro q hq
      have he := congrArg Subtype.val (hab (⟨q,hq⟩ : Q))
      change (a : G) * q * (a : G)⁻¹ = (b : G) * q * (b : G)⁻¹ at he
      have hh : (a : G)⁻¹ * b * q * ((a : G)⁻¹ * b)⁻¹ = q := by
        calc
          _ = (a : G)⁻¹ * ((b : G) * q * (b : G)⁻¹) * a := by group
          _ = q := by rw [← he]; group
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have he : (a : G)⁻¹ * b = 1 := hf.le ⟨P.mul_mem (P.inv_mem a.property) b.property, hc⟩
    exact inv_mul_eq_one.mp he
  have he : FixedPoints.subgroup (center P) Q =
      (centralizer ((center P).map P.subtype : Set G)).subgroupOf Q := by
    ext q
    constructor
    · intro h z hz
      obtain ⟨z,hz,rfl⟩ := hz
      have hh := congrArg Subtype.val (h ⟨z,hz⟩)
      change (z : G) * q * (z : G)⁻¹ = q at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro h z
      apply Subtype.ext
      change ((z : P) : G) * q * ((z : P) : G)⁻¹ = q
      have hh : ((z : P) : G) * (q : G) = (q : G) * ((z : P) : G) :=
        h _ (mem_map_of_mem _ z.property)
      rw [hh, mul_inv_cancel_right]
  rw [relIndex, ← he]
  exact fixedIndex_lower_bound hP hQ
end ExtraspecialQuinticCenter
