module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Model
public import Theory.GroupTheory.NormalProductCoordinate
public import Theory.Alternating.Aut
/-!
# Automorphisms of the alternating-five product

Simplicity and the trivial center force every automorphism to preserve or
exchange the two factors. Restricting the coordinate homomorphisms then gives
two actual factor automorphisms. This supplies the group-theoretic input to
the deleted tensor normalizer in Aschbacher–Smith D.3.7, pp.197–199.
-/
public section
open Subgroup Theory.GroupTheory
namespace BinaryPermutation.FiveTensorSquare
private theorem normal_quotient_two (N : Subgroup Alt) [N.Normal] (hN : N ≠ ⊥) :
    IsPGroup 2 (Alt ⧸ N) := by
  have he : N = ⊤ := (Subgroup.Normal.eq_bot_or_eq_top (H := N) inferInstance).resolve_left hN
  subst N
  let : Subsingleton (Alt ⧸ (⊤ : Subgroup Alt)) := QuotientGroup.subsingleton_quotient_top
  exact IsPGroup.of_subsingleton _ _
private theorem alt_twoCore : pCore 2 Alt = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (H := pCore 2 Alt) inferInstance with h | h
  · exact h
  · have hc : Nat.card (pCore 2 Alt) = 60 := by
      rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv]
      change Nat.card (alternatingGroup (Fin 5)) = 60
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Alt)).exists_card_eq
    have ht : 3 ∣ 2 ^ n := hn ▸ hc ▸ (by decide : 3 ∣ 60)
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow ht) |>.elim
private theorem product_coordinates (φ : MulAut (Alt × Alt)) :
    ((∀ a, (φ (a,1)).2 = 1) ∧ (∀ b, (φ (1,b)).1 = 1)) ∨
      ((∀ a, (φ (a,1)).1 = 1) ∧ (∀ b, (φ (1,b)).2 = 1)) :=
  automorphism_product_coordinates normal_quotient_two normal_quotient_two alt_twoCore
    (alternatingGroup.center_eq_bot (by simp)) φ
private theorem split_product (φ : MulAut (Alt × Alt))
    (ha : ∀ a, (φ (a,1)).2 = 1) (hb : ∀ b, (φ (1,b)).1 = 1) :
    ∃ α β : MulAut Alt, ∀ g, φ g = (α g.1, β g.2) := by
  let qa := (MonoidHom.fst Alt Alt).comp (φ.toMonoidHom.comp (MonoidHom.inl Alt Alt))
  let qb := (MonoidHom.snd Alt Alt).comp (φ.toMonoidHom.comp (MonoidHom.inr Alt Alt))
  have hi : Function.Injective qa := by
    intro a b hab
    exact congrArg Prod.fst (φ.injective (Prod.ext hab ((ha a).trans (ha b).symm)))
  have hj : Function.Injective qb := by
    intro a b hab
    exact congrArg Prod.snd (φ.injective (Prod.ext ((hb a).trans (hb b).symm) hab))
  refine ⟨MulEquiv.ofBijective qa ⟨hi,Finite.surjective_of_injective hi⟩,
    MulEquiv.ofBijective qb ⟨hj,Finite.surjective_of_injective hj⟩, ?_⟩
  intro g
  have hg : g = (g.1,1) * (1,g.2) := by simp
  conv_lhs => rw [hg, map_mul]
  apply Prod.ext
  · change (φ (g.1,1)).1 * (φ (1,g.2)).1 = _
    rw [hb, mul_one]
    rfl
  · change (φ (g.1,1)).2 * (φ (1,g.2)).2 = _
    rw [ha, one_mul]
    rfl

theorem product_automorphism_alternatives (φ : MulAut (Alt × Alt)) :
    (∃ α β : MulAut Alt, ∀ g, φ g = (α g.1, β g.2)) ∨
    (∃ α β : MulAut Alt, ∀ g, φ g = (α g.2, β g.1)) := by
  rcases product_coordinates φ with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl (split_product φ ha hb)
  · let ψ := MulEquiv.prodComm.trans φ
    obtain ⟨α,β,h⟩ := split_product ψ hb ha
    refine Or.inr ⟨α,β,fun g => ?_⟩
    exact h (g.2,g.1)
end BinaryPermutation.FiveTensorSquare
