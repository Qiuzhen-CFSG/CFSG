module

public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# Transfer to the three possible involution classes

In Aschbacher--Smith 15.3.38, printed pp.1136--1137, the subgroup
`W = ⟨w, S_L⟩` has index two in the Sylow two-group and `W/S_L` is cyclic
of order four, with `f = w²`. Thompson transfer supplies a conjugate of
`τ` in `W`. Its image in the cyclic quotient is either the identity or
`f`, so the local involution classes reduce ambient fusion to `f`, `v`,
or `z`.

The quotient is represented by a homomorphism to the concrete cyclic
four-group with its actual kernel and specified image of `f`. The local
class-cover hypotheses must come from the central-cover model. The proof
derives the transfer conclusion from `G = O²(G)` and proves the cyclic
quotient step; neither is included among the assumptions.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter

open Subgroup

variable {G : Type*} [Group G]

/-- Transfer and the cyclic-four quotient restrict fusion to the three source classes. -/
theorem transfer_fusion_trichotomy [Finite G]
    (T : Sylow 2 G) (hG : IsPPerfect 2 G)
    (W : Subgroup T) (hW : W.index = 2)
    (q : W →* Multiplicative (ZMod 4)) (L : Subgroup G)
    (hker : ∀ x : W, q x = 1 ↔ ((x : T) : G) ∈ L)
    (f : W) (hf : q f = Multiplicative.ofAdd (2 : ZMod 4))
    (τ : T) (hτ : orderOf τ = 2) (v z : G)
    (hinside : ∀ x : G, x ∈ L → orderOf x = 2 → IsConj x v ∨ IsConj x z)
    (hcoset : ∀ x : G, orderOf x = 2 → x * (((f : T) : G))⁻¹ ∈ L →
      IsConj x (((f : T) : G))) :
    IsConj (τ : G) (((f : T) : G)) ∨ IsConj (τ : G) v ∨ IsConj (τ : G) z := by
  have hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2 := by
    intro K hK he
    let : K.Normal := hK
    have hp : IsPGroup 2 (G ⧸ K) := IsPGroup.of_card (n := 1) (by simpa only [pow_one, ← index_eq_card] using he)
    have hle : pResidual 2 G ≤ K := sInf_le ⟨hK, hp⟩
    rw [(pResidual_eq_top_iff 2 G).mpr hG] at hle
    have htop : K = ⊤ := top_unique hle
    simp [htop] at he
  obtain ⟨u, hτu, huW⟩ := T.exists_isConj_mem_of_index_two hno W hW τ hτ
  have huo : orderOf (u : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hτu
    have he : (MulAut.conj g) (τ : G) = u := hg
    rw [← he, MulEquiv.orderOf_eq, orderOf_coe, hτ]
  let a : W := ⟨u, huW⟩
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact (orderOf_eq_prime_iff.mp huo).1
  have hq2 : (q a) ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  have hclass : q a = 1 ∨ q a = Multiplicative.ofAdd (2 : ZMod 4) := by
    exact (by decide : ∀ b : Multiplicative (ZMod 4), b ^ 2 = 1 →
      b = 1 ∨ b = Multiplicative.ofAdd (2 : ZMod 4)) (q a) hq2
  rcases hclass with hk | hf'
  · rcases hinside u ((hker a).mp hk) huo with hv | hz
    · exact Or.inr (Or.inl (hτu.trans hv))
    · exact Or.inr (Or.inr (hτu.trans hz))
  · have hcos : (u : G) * (((f : T) : G))⁻¹ ∈ L := by
      apply (hker (a * f⁻¹)).mp
      rw [map_mul, map_inv, hf', hf, mul_inv_cancel]
    exact Or.inl (hτu.trans (hcoset u huo hcos))



end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
