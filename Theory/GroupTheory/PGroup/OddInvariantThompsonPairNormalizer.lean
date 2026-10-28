module

public import Theory.GroupTheory.PGroup.InvariantThompsonPairNormalizer

/-!
# Odd-order transport of a two-member invariant maximum family

The family of maximum elementary subgroups that are normalized by `R` may be
strictly smaller than the full maximum family of `R`.  If that restricted
family is a pair, the normalizer of `R` still permutes the pair.  An odd-order
subgroup of the normalizer cannot move either member, since a moved member has
normalizer relative index two.

This is the source interface used for the G₂ terminal argument: the source
proves only `{B ∈ A(R) | R ≤ N(B)} = {Q,W}`, rather than
`A(R) = {Q,W}`.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- An odd-order subgroup normalizing `R` fixes both members of the pair of
`R`-normal maximum elementary subgroups. -/
theorem odd_normalizes_invariant_maxFamily_pair
    (R D Q W : Subgroup G)
    (hfamily : {A | A ∈ elementaryAbelianMaxSubgroups R ∧
      R ≤ normalizer (A : Set G)} = {Q,W})
    (hD : D ≤ normalizer (R : Set G))
    (hodd : Odd (Nat.card D)) :
    D ≤ normalizer (Q : Set G) ∧ D ≤ normalizer (W : Set G) := by
  have hfix (P S : Subgroup G)
      (hpair : ∀ g ∈ D,
        P.map (MulAut.conj g).toMonoidHom = P ∨
          P.map (MulAut.conj g).toMonoidHom = S) :
      D ≤ normalizer (P : Set G) := by
    intro g hg
    by_contra hmove
    have hne : P.map (MulAut.conj g).toMonoidHom ≠ P := by
      intro he
      exact hmove (mem_normalizer_iff_map_conj_eq.mpr he)
    have hi := Subgroup.normalizer_relIndex_eq_two_of_pair D P S hpair g hg hne
    have hdiv : 2 ∣ Nat.card D := hi ▸
      (normalizer (P : Set G)).relIndex_dvd_card D
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  have hpairQ : ∀ g ∈ D,
      Q.map (MulAut.conj g).toMonoidHom = Q ∨
        Q.map (MulAut.conj g).toMonoidHom = W := by
    intro g hg
    exact normalizer_preserves_invariant_maxFamily_pair R Q W hfamily (hD hg)
  have hpairW : ∀ g ∈ D,
      W.map (MulAut.conj g).toMonoidHom = W ∨
        W.map (MulAut.conj g).toMonoidHom = Q := by
    intro g hg
    exact normalizer_preserves_invariant_maxFamily_pair R W Q
      (hfamily.trans (Set.pair_comm Q W)) (hD hg)
  exact ⟨hfix Q W hpairQ, hfix W Q hpairW⟩

end Theory.GroupTheory
end
