module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# Conjugate intersections and a prime commutator subgroup

Suppose Q lies in X and [Q,Q] lies in a prime-order subgroup Z. If
|Q|² exceeds |X| times the largest possible abelian-subgroup order in Q,
then every intersection Q ∩ Qˣ is nonabelian. Its nontrivial derived
subgroup lies in both Z and Zˣ, so the two prime-order groups coincide.
Consequently X normalizes Z.

The relative-index inequality counts the intersection without assuming
normality of Q in X. This is the local counting argument used to exclude
a class-two small core in the original Aschbacher--Smith F.1.12 geometry.
-/

public section
namespace Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Large nonabelian conjugate intersections force normalization of a prime derived layer. -/
theorem le_normalizer_of_prime_commutator_and_abelian_bound
    (X Q Z : Subgroup G) (bound : ℕ)
    (hQX : Q ≤ X) (hcomm : ⁅Q,Q⁆ ≤ Z) (hprime : Nat.Prime (Nat.card Z))
    (hbound : ∀ A : Subgroup G, IsMulCommutative A → A ≤ Q → Nat.card A ≤ bound)
    (horder : Nat.card X * bound < Nat.card Q * Nat.card Q) :
    X ≤ normalizer (Z : Set G) := by
  intro x hx
  let f := (MulAut.conj x).toMonoidHom
  let Qx := Q.map f
  let K := Q ⊓ Qx
  have hQxX : Qx ≤ X := by
    rintro _ ⟨q,hq,rfl⟩
    exact X.mul_mem (X.mul_mem hx (hQX hq)) (X.inv_mem hx)
  have hQxcard : Nat.card Qx = Nat.card Q :=
    card_map_of_injective (MulAut.conj x).injective
  have hKcard : Nat.card Q * Nat.card Q ≤ Nat.card X * Nat.card K := by
    have hi : K.relIndex Q ≤ Qx.relIndex X := by
      change (Q ⊓ Qx).relIndex Q ≤ _
      rw [inf_relIndex_left]
      exact relIndex_le_of_le_right hQX index_ne_zero_of_finite
    have hk := (K.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show K ≤ Q from inf_le_left)).toEquiv] at hk
    change K.relIndex Q * Nat.card K = Nat.card Q at hk
    have hX := (Qx.subgroupOf X).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hQxX).toEquiv,hQxcard] at hX
    change Qx.relIndex X * Nat.card Q = Nat.card X at hX
    calc
      Nat.card Q * Nat.card Q = (K.relIndex Q * Nat.card K) * Nat.card Q := by rw [hk]
      _ ≤ (Qx.relIndex X * Nat.card K) * Nat.card Q :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)
      _ = (Qx.relIndex X * Nat.card Q) * Nat.card K := by ring
      _ = _ := by rw [hX]
  have hn : ⁅K,K⁆ ≠ ⊥ := by
    intro heq
    have hab := commutator_self_eq_bot_iff.mp heq
    have hb := hbound K hab inf_le_left
    exact (Nat.not_lt_of_ge (hKcard.trans (Nat.mul_le_mul_left _ hb))) horder
  have hKZ : ⁅K,K⁆ ≤ Z := (commutator_mono inf_le_left inf_le_left).trans hcomm
  have hKeq : ⁅K,K⁆ = Z := by
    apply eq_of_le_of_card_ge hKZ
    have hd := card_dvd_of_le hKZ
    rcases hprime.eq_one_or_self_of_dvd _ hd with hone | heq
    · exact (hn (card_eq_one.mp hone)).elim
    · exact heq.ge
  have hKZx : ⁅K,K⁆ ≤ Z.map f := by
    apply (commutator_mono (show K ≤ Qx from inf_le_right) inf_le_right).trans
    change ⁅Q.map f,Q.map f⁆ ≤ Z.map f
    rw [← map_commutator]
    exact map_mono hcomm
  have hZZx : Z ≤ Z.map f := hKeq ▸ hKZx
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (eq_of_le_of_card_ge hZZx (by rw [card_map_of_injective (MulAut.conj x).injective])).symm

end Subgroup
