module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.SmallLinear
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import GorensteinWalter.PSL2CoprimeSylowCyclic

/-!
# Odd-characteristic PSL₂ pair exclusion

For a field of order p or p² with p > 3, the Sylow three-subgroups of the
concrete PSL₂ model are cyclic. At field orders at least seven this follows
from the proved split and nonsplit torus calculation; at field order five
the group has order 60 and its Sylow three-subgroups have order three.
Transport through the supplied multiplicative equivalence and the central
image reduction then exclude a nonreducible pair in every central cover.
Indeed, its central image would have order nine or 27 and exponent dividing
three, which is impossible in a cyclic three-subgroup.

For p = 3 the parameter restrictions force field order nine, where the
permuting-product exclusion from `SmallLinear` applies. No assumption about
the Schur multiplier or the order of the center is needed in either branch.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528), the odd-characteristic L₂ cases.
The torus calculation is `GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card`,
proved from the concrete Huppert II.8.3–8.5 interfaces.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical

private theorem cyclic_three_sylow_of_field_card_five
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 5)
    (P : Sylow 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    IsCyclic P := by
  have hcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 60 := by
    have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
    rw [hF] at hh
    norm_num [Fin.prod_univ_succ] at hh
    omega
  apply isCyclic_of_prime_card (p := 3)
  rw [P.card_eq_multiplicity, hcard, show 60 = 3 * 20 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 20)]
  norm_num

private theorem cyclic_three_sylow_of_field_card_prime_pow
    {F : Type*} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (ho : Odd p) (he : e = 1 ∨ e = 2) (hlt : 3 < p)
    (hF : Nat.card F = p ^ e)
    (P : Sylow 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    IsCyclic P := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hseven : 7 ≤ Nat.card F
  · apply GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF hseven
      3 (by decide) _ P
    rw [hF]
    exact ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega)).pow_right e
  · apply cyclic_three_sylow_of_field_card_five (P := P)
    rcases he with rfl | rfl
    · rw [pow_one] at hF
      obtain ⟨k, hk⟩ := ho
      omega
    · rw [pow_two] at hF
      nlinarith

/-- The odd PSL₂ cases in Theorem C give reducible Sylow pairs, including
every quasisimple central cover of the specified projective model. -/
theorem reducible_of_psl_two_odd {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hsimple : 4 ≤ p ^ e) (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 2 (p ^ e)) :
    PairReducible (S : Subgroup Q) R := by
  by_cases hp3 : p = 3
  · subst p
    have he2 : e = 2 := by rcases he with rfl | rfl <;> norm_num at *
    subst e
    exact reducible_of_psl_two_nine h (by simpa using hm)
  · have hlt : 3 < p := by
      have hp2 := hp.two_le
      obtain ⟨k, hk⟩ := ho
      omega
    obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
    apply reducible_of_cyclic_three_sylow h
    intro P
    let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
    have hc : IsCyclic P' :=
      cyclic_three_sylow_of_field_card_prime_pow hp ho he hlt hF P'
    have hcmap : IsCyclic ((P : Subgroup (Q ⧸ center Q)).map a.toMonoidHom) := by
      exact hc
    exact (a.subgroupMap (P : Subgroup (Q ⧸ center Q))).isCyclic.mpr hcmap

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
