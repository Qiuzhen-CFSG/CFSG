module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Frames
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.PermutationAction
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.NormalizerAction.QuotientActions

/-!
# Full frame-torus normalizers and their S₃ actions

For the literal special and projective frame tori over the field of order
`(2ⁿ)²`, with fixed field of order `2ⁿ` and `n ≥ 2`, this module supplies
surjective geometric permutation homomorphisms, their exact relative torus
kernels, and equivalences of the relative normalizer quotients with S₃.
Every normalizer element satisfies the published conjugation formula on
`specialPairHom` or `projectivePairHom` in the same supplied frame.

The geometric identification and permutation representatives are proved in
the imported descendants. The torus has odd order, so an involution cannot
lie in the permutation kernel. Its image is therefore an order-two
permutation. These are the explicit action inputs for the independent
fixed-subgroup and commutator calculations; none of those calculations is
assumed here.

Source: GLS4, Chapter 4, Lemma 3.11(c),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603, as used by Chapter 2,
Lemma 17.4, `refs/KGroup/GLS4/Chapter2.tex`, lines 3136–3147.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.IdentityGram HermitianForm.EvenInner
open scoped Pointwise
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]

private theorem action_order_two_of_odd_torus {G Q : Type*} [Group G] [Group Q]
    (H : Subgroup G) (f : normalizer (G := G) H →* Q)
    (hker : f.ker = H.subgroupOf (normalizer H)) (hodd : Odd (Nat.card H))
    (t : normalizer (G := G) H) (ht : orderOf t = 2) : orderOf (f t) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  · intro hf
    have hm : t.val ∈ H := by
      change t ∈ H.subgroupOf (normalizer H)
      rw [← hker]
      exact hf
    have he : orderOf (⟨t.val, hm⟩ : H) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, ht]
    have hd := orderOf_dvd_natCard (⟨t.val, hm⟩ : H)
    rw [he] at hd
    exact hodd.not_two_dvd_nat hd

private theorem binary_frame_size_ge_two (n : ℕ) (hn : 2 ≤ n) : 2 ≤ 2 ^ n :=
  (by decide : 2 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by decide) hn)

theorem specialFrameTorus_odd_card [Finite E]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    Odd (Nat.card (specialFrameTorus J P)) := by
  rw [specialFrameTorus_card J P (2 ^ n) hcard hfixed]
  exact ((even_two.pow_of_ne_zero (by omega : n ≠ 0)).add_one).pow

theorem projectiveFrameTorus_odd_card [Finite E]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    Odd (Nat.card (projectiveFrameTorus J P)) :=
  (specialFrameTorus_odd_card J P n hn hcard hfixed).of_dvd_nat
    ((specialFrameTorus J P).card_map_dvd J.specialToProjective)

section Binary
variable [Finite E] (J : HermitianForm 3 E) (P : OrthogonalFrame J) (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
include n hn hcard hfixed

/-- The full special normalizer has the required onto geometric action, with
its relative torus kernel, and sends each involution to an involution. -/
theorem specialFrameNormalizer_action :
    ∃ f : normalizer (G := J.specialSubgroup) (specialFrameTorus J P) →* Equiv.Perm (Fin 3),
      Function.Surjective f ∧
      f.ker = (specialFrameTorus J P).subgroupOf (normalizer (specialFrameTorus J P)) ∧
      (∀ g, HasSpecialFrameAction J P g.val (f g)) ∧
      ∀ t, orderOf t = 2 → orderOf (f t) = 2 := by
  let := frame_char_two (E := E) n hcard
  let f := specialNormalizerAction J P (2 ^ n) (binary_frame_size_ge_two n hn) hcard hfixed
  refine ⟨f, specialNormalizerAction_surjective J P _ _ _ _,
    specialNormalizerAction_ker J P _ _ _ _, specialNormalizerAction_action J P _ _ _ _, ?_⟩
  exact action_order_two_of_odd_torus _ f (specialNormalizerAction_ker J P _ _ _ _)
    (specialFrameTorus_odd_card J P n hn hcard hfixed)

/-- The projective action retains the full scalar quotient and the relative
projective torus kernel. -/
theorem projectiveFrameNormalizer_action :
    ∃ f : normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P) →*
        Equiv.Perm (Fin 3),
      Function.Surjective f ∧
      f.ker = (projectiveFrameTorus J P).subgroupOf (normalizer (projectiveFrameTorus J P)) ∧
      (∀ g, HasProjectiveFrameAction J P g.val (f g)) ∧
      ∀ t, orderOf t = 2 → orderOf (f t) = 2 := by
  let := frame_char_two (E := E) n hcard
  let f := projectiveNormalizerAction J P (2 ^ n) (binary_frame_size_ge_two n hn) hcard hfixed
  refine ⟨f, projectiveNormalizerAction_surjective J P _ _ _ _,
    projectiveNormalizerAction_ker J P _ _ _ _, projectiveNormalizerAction_action J P _ _ _ _, ?_⟩
  exact action_order_two_of_odd_torus _ f (projectiveNormalizerAction_ker J P _ _ _ _)
    (projectiveFrameTorus_odd_card J P n hn hcard hfixed)

/-- The literal relative quotient N_SU(F)/F is S₃, with no additional
characteristic or action premise. -/
noncomputable def specialFrameNormalizerEquivPerm :
    (normalizer (G := J.specialSubgroup) (specialFrameTorus J P) ⧸
      (specialFrameTorus J P).subgroupOf (normalizer (specialFrameTorus J P))) ≃*
        Equiv.Perm (Fin 3) := by
  let := frame_char_two (E := E) n hcard
  exact specialNormalizerQuotientEquiv J P (2 ^ n) (binary_frame_size_ge_two n hn) hcard hfixed

/-- The literal relative quotient N_PSU(F)/F is S₃. -/
noncomputable def projectiveFrameNormalizerEquivPerm :
    (normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P) ⧸
      (projectiveFrameTorus J P).subgroupOf (normalizer (projectiveFrameTorus J P))) ≃*
        Equiv.Perm (Fin 3) := by
  let := frame_char_two (E := E) n hcard
  exact projectiveNormalizerQuotientEquiv J P (2 ^ n) (binary_frame_size_ge_two n hn) hcard hfixed

theorem specialFrameNormalizer_involution_action
    (t : normalizer (G := J.specialSubgroup) (specialFrameTorus J P)) (ht : orderOf t = 2) :
    ∃ σ : Equiv.Perm (Fin 3), orderOf σ = 2 ∧ HasSpecialFrameAction J P t.val σ := by
  obtain ⟨f, _, _, hact, hord⟩ := specialFrameNormalizer_action J P n hn hcard hfixed
  exact ⟨f t, hord t ht, hact t⟩

theorem projectiveFrameNormalizer_involution_action
    (t : normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P))
    (ht : orderOf t = 2) :
    ∃ σ : Equiv.Perm (Fin 3), orderOf σ = 2 ∧ HasProjectiveFrameAction J P t.val σ := by
  obtain ⟨f, _, _, hact, hord⟩ := projectiveFrameNormalizer_action J P n hn hcard hfixed
  exact ⟨f t, hord t ht, hact t⟩

end Binary

end UnitaryThree.OddTorusNormalizer
