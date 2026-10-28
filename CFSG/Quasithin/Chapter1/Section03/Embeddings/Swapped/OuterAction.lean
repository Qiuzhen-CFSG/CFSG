module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.OuterAction.QuotientAction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.OuterAction.TwoFactors

/-!
# Even single-factor outer order from the swapped action

Let N be normal in the finite group M and T a Sylow two-subgroup. Suppose an
odd p-subgroup P lies in N, its image in N/O₂(N) normalizes the Sylow image,
and N/O₂(N) is explicitly isomorphic to Q × Q for a nonabelian simple Q.
If the automizer induced by N_T(P) has nontrivial Frattini subgroup, Out(Q)
has even order.

The actual quotient-conjugation action has outer kernel centralizing P.
Its outer image therefore has the automizer as a quotient. If Out(Q) had
odd order, the proved two-factor order formula would bound this outer
image, and hence the automizer, by two. Such a group has trivial Frattini
subgroup, giving the contradiction.

This is the conditional group-theoretic implication in the swapped branch;
the product isomorphism and the quotient-normalization hypothesis are
explicit inputs for its source-theorem consumer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.510.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedOuter

private theorem frattini_trivial_of_card_le_two {A : Type*} [Group A] [Finite A]
    (hc : Nat.card A ≤ 2) : frattini A = ⊥ := by
  by_cases h : frattini A = ⊥
  · exact h
  have hn := (frattini A).one_lt_card_iff_ne_bot.mpr h
  have ht : frattini A = ⊤ := Subgroup.eq_of_le_of_card_ge le_top (by
    rw [Subgroup.card_top]
    omega)
  have hb : (⊥ : Subgroup A) = ⊤ := frattini_nongenerating (by simp [ht])
  exact ht.trans hb.symm

variable {M Q : Type*} [Group M] [Finite M] [Group Q] [Finite Q]
  [IsSimpleGroup Q] [Group.IsPerfect Q]

/-- The genuine outer action forces even single-factor outer order. -/
theorem even_outer_order_of_frattini_automizer (N : Subgroup M) [N.Normal]
    (T : Sylow 2 M) {p : ℕ} [Fact p.Prime] (P : Subgroup M)
    (hp : Odd p) (hP : IsPGroup p P) (hPN : P ≤ N)
    (e : (N ⧸ pCore 2 N) ≃* Q × Q)
    (hn : Image N P ≤ normalizer (Image N T))
    (hPhi : frattini (automizer T P) ≠ ⊥) : Even (Nat.card (MulAut.Outer Q)) := by
  by_contra heven
  have hodd : Odd (Nat.card (MulAut.Outer Q)) := Nat.not_even_iff_odd.mp heven
  let A := (T : Subgroup M) ⊓ normalizer P
  let f := outerAction N T P
  let a : A →* MulAut P := P.normalizerMonoidHom.comp (inclusion inf_le_right)
  have hker : f.ker ≤ a.rangeRestrict.ker := by
    intro t ht
    apply Subtype.ext
    change a t = 1
    have hc := outer_kernel_centralizes N T P hp hP hPN hn
      (center_eq_bot_of_product_equiv e) ht
    have hh : (inclusion (show A ≤ normalizer P from inf_le_right)) t ∈
        P.normalizerMonoidHom.ker := by
      rw [normalizerMonoidHom_ker]
      exact hc
    exact hh
  let g := QuotientGroup.lift f.ker a.rangeRestrict hker
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective
    f.ker a.rangeRestrict a.rangeRestrict_surjective hker
  have htwo : IsPGroup 2 f.range :=
    T.isPGroup'.to_inf_left.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hbound : Nat.card f.range ≤ 2 := outer_two_subgroup_card_le_two e hodd f.range htwo
  have hquot : Nat.card (A ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hauto : Nat.card (automizer T P) ≤ 2 := by
    apply (Nat.card_le_card_of_surjective g hg).trans
    rw [hquot]
    exact hbound
  exact hPhi (frattini_trivial_of_card_le_two hauto)

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedOuter
