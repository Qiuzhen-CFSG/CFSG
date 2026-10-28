module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Group


/-!
# Inner quaternion restrictions from a fixed elementary eight

Let two commuting quaternion subgroups generate an order32 group. An ambient
actor preserving both factors and fixing pointwise an elementary subgroup of
order eight acts by an inner automorphism on either quaternion factor. The
statement uses the exponent-two property explicitly and does not assume any
ambient group classification or geometry.

A quaternion group contains only two elements whose square is one. Thus the
fixed elementary eight meets the other quaternion factor in order at most two,
and their product is the whole order32 join. Writing an element b of the first
factor as a*c, with a fixed, shows that b⁻¹e(b)=c⁻¹e(c) lies in both factors.
It is central in the first factor, so the quaternion central-automorphism
calculation makes the restriction inner.

This source-neutral step is used in Stellmacher(9.1), Journal of Algebra190
(1997), p.48, to exclude preservation of both factors by an outside initial
center actor. It is extracted unchanged from the checked distance-one
factor-swap proof so the earlier terminal-core calculation can reuse it.
-/

namespace Subgroup
private theorem factor_central_difference_of_fixed_eight
    {G : Type*} [Group G] [Finite G] (B C A : Subgroup G)
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hVcard : Nat.card (B ⊔ C : Subgroup G) = 32)
    (hA : A ≤ B ⊔ C) (hAcard : Nat.card A = 8)
    (hAexp : ∀ a ∈ A, a ^ 2 = 1)
    (e : G ≃* G) (hBn : B.map e.toMonoidHom = B) (hCn : C.map e.toMonoidHom = C)
    (hfix : ∀ a ∈ A, e a = a) :
    ∀ b ∈ B, b⁻¹ * e b ∈ B ⊓ C := by
  obtain ⟨eC⟩ := hC
  have hCcard : Nat.card C = 8 := by
    rw [Nat.card_congr eC.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hinter : Nat.card (C ⊓ A : Subgroup G) ≤ 2 := by
    let roots := {x : QuaternionGroup 2 // x ^ 2 = 1}
    have hroots : Nat.card roots = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    let f : (C ⊓ A : Subgroup G) → roots := fun x =>
      ⟨eC ⟨x, x.property.1⟩, by
        rw [← map_pow]
        have hh : (⟨x, x.property.1⟩ : C) ^ 2 = 1 := Subtype.ext (hAexp x x.property.2)
        rw [hh, map_one]⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have hh := eC.injective (congrArg Subtype.val hxy)
      exact Subtype.ext (congrArg (fun v : C => (v : G)) hh)
    exact hroots ▸ Nat.card_le_card_of_injective f hf
  have hnorm : A ≤ Subgroup.normalizer (C : Set G) := by
    apply hA.trans
    apply sup_le ?_ C.le_normalizer
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hsup : C ⊔ A = B ⊔ C := by
    have hle : C ⊔ A ≤ B ⊔ C := sup_le le_sup_right hA
    have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes C A hnorm
    have hbound := Subgroup.card_le_of_le hle
    rw [hCcard, hAcard] at hcard
    rw [hVcard] at hbound
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hVcard]
    nlinarith
  intro b hb
  have hbAC : b ∈ A ⊔ C := by rw [sup_comm, hsup]; exact Subgroup.mem_sup_left hb
  have hbprod : b ∈ (↑(A ⊔ C) : Set G) := hbAC
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A C hnorm] at hbprod
  obtain ⟨a, ha, c, hc, hprod⟩ := hbprod
  refine ⟨B.mul_mem (B.inv_mem hb) (hBn ▸ Subgroup.mem_map_of_mem e.toMonoidHom hb), ?_⟩
  have hec : e c ∈ C := hCn ▸ Subgroup.mem_map_of_mem e.toMonoidHom hc
  have heq : b⁻¹ * e b = c⁻¹ * e c := by
    rw [← hprod, map_mul, hfix a ha]
    group
  rw [heq]
  exact C.mul_mem (C.inv_mem hc) hec


public theorem factor_inner_of_fixed_eight
    {G : Type*} [Group G] [Finite G] (B C A : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hVcard : Nat.card (B ⊔ C : Subgroup G) = 32)
    (hA : A ≤ B ⊔ C) (hAcard : Nat.card A = 8)
    (hAexp : ∀ a ∈ A, a ^ 2 = 1)
    (actor : G) (hBn : actor ∈ Subgroup.normalizer (B : Set G))
    (hCn : actor ∈ Subgroup.normalizer (C : Set G))
    (hfix : ∀ a ∈ A, Commute actor a) :
    ∃ b : G, b ∈ B ∧ ∀ x ∈ B, actor * x * actor⁻¹ = b * x * b⁻¹ := by
  obtain ⟨model⟩ := hB
  let act : MulAut B := B.normalizerMonoidHom ⟨actor, hBn⟩
  have hdiff := factor_central_difference_of_fixed_eight B C A hC hcomm hVcard
    hA hAcard hAexp (MulAut.conj actor)
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hBn)
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hCn) (by
      intro a ha
      change actor * a * actor⁻¹ = a
      rw [(hfix a ha).eq, mul_inv_cancel_right])
  have hcentral : ∀ x : B, x⁻¹ * act x ∈ Subgroup.center B := by
    intro x
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hcomm y y.property _ (hdiff x x.property).2
  obtain ⟨b, hb⟩ := QuaternionGroup.exists_conj_of_central_difference_of_equiv model act hcentral
  refine ⟨b, b.property, ?_⟩
  intro x hx
  exact congrArg (fun f : MulAut B => (f ⟨x, hx⟩ : G)) hb

end Subgroup
