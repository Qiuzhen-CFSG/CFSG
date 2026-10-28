module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A fused unique involution forces a normal core to have order two

Let U and P be normal subgroups of a finite two-group. Suppose U has a
unique involution and an automorphism moves it outside U and P. Its image
Uᵃ is disjoint from both normal subgroups, so centralizes P. If C(P) lies
in Q U, where Q is elementary abelian and centralizes U, every square of
Uᵃ lies in U and is therefore trivial. Uniqueness then gives |U|=2.

This is the two-group argument in GLS IV, Chapter 2, Lemma 16.6(b).
-/

namespace Subgroup
variable {T : Type*} [Group T] [Finite T]

private theorem disjoint_of_unique_involution_not_mem
    (hT : IsPGroup 2 T) (W H : Subgroup T) (w : T)
    (huniq : ∀ x ∈ W, orderOf x = 2 → x = w) (hw : w ∉ H) :
    Disjoint W H := by
  apply disjoint_iff.mpr
  by_contra hne
  let I := W ⊓ H
  let : Nontrivial I := (I.nontrivial_iff_ne_bot).mpr hne
  obtain ⟨n, hn, hc⟩ := (hT.to_subgroup I).nontrivial_iff_card.mp inferInstance
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := I) 2
    (by rw [hc]; exact dvd_pow_self 2 (by omega))
  have he := huniq x x.property.1 (by simpa using hx)
  exact hw (he ▸ x.property.2)

/-- The original normal two-group configuration forces its unique-involution
core to have order two. All movement and centralizer hypotheses are literal. -/
public theorem card_eq_two_of_fused_unique_involution
    (hT : IsPGroup 2 T) (U P Q : Subgroup T) [U.Normal] [P.Normal]
    [IsElementaryAbelian 2 Q] (u : T) (hu : u ∈ U) (hu2 : orderOf u = 2)
    (huniq : ∀ v ∈ U, orderOf v = 2 → v = u)
    (a : MulAut T) (hne : a u ≠ u) (hout : a u ∉ P)
    (hQ : Q ≤ centralizer (U : Set T))
    (hcent : centralizer (P : Set T) ≤ Q ⊔ U) : Nat.card U = 2 := by
  let W := U.map a.toMonoidHom
  let : W.Normal := (inferInstance : U.Normal).map a.toMonoidHom a.surjective
  have hw : a u ∈ W := mem_map_of_mem a.toMonoidHom hu
  have hw2 : orderOf (a u) = 2 := by simpa using hu2
  have hwu (x : T) (hx : x ∈ W) (hx2 : orderOf x = 2) : x = a u := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact congrArg a (huniq y hy (by simpa using hx2))
  have hnotU : a u ∉ U := fun hh => hne (huniq (a u) hh hw2)
  have hWP := disjoint_of_unique_involution_not_mem hT W P (a u) hwu hout
  have hWU := disjoint_of_unique_involution_not_mem hT W U (a u) hwu hnotU
  have hWC : W ≤ centralizer (P : Set T) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hWP)
  have hsquare (x : T) (hx : x ∈ W) : x ^ 2 = 1 := by
    obtain ⟨q, hq, v, hv, he⟩ := mem_sup_of_normal_right.mp (hcent (hWC hx))
    have hq2 : q ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p (p := 2) (G := Q)) ⟨q, hq⟩)
    have hcomm : Commute q v :=
      (mem_centralizer_iff.mp (hQ hq) v hv).symm
    have hx2U : x ^ 2 ∈ U := by
      rw [← he, hcomm.mul_pow, hq2, one_mul]
      exact U.pow_mem hv 2
    exact disjoint_def.mp hWU (W.pow_mem hx 2) hx2U
  have hcardW : Nat.card W = 2 := by
    apply (Nat.card_eq_two_iff' (1 : W)).mpr
    refine ⟨⟨a u, hw⟩, ?_, ?_⟩
    · intro hh
      have he : a u = 1 := congrArg Subtype.val hh
      rw [he, orderOf_one] at hw2
      omega
    · intro x hx
      apply Subtype.ext
      exact hwu x x.property (orderOf_eq_prime (hsquare x x.property)
        (fun hh => hx (Subtype.ext hh)))
  rw [card_map_of_injective a.injective] at hcardW
  exact hcardW

end Subgroup
