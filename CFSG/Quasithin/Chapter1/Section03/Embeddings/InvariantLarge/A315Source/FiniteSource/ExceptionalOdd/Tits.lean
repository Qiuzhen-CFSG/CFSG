module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.Reduction
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders

/-!
# The Tits carrier has no permuting full Sylow pair at five

The checked double-coset coverage places every proper subgroup containing
the full Sylow two-subgroup in one of the two actual parabolics. Neither
parabolic order is divisible by 25. The original component is transported
through the literal Parrott-to-permutation equivalence.

Source: Aschbacher–Smith, Proposition 1.3.4, printed pp.510–511,
using the original full Sylow hypothesis in A.3.15.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
open Tits Tits.ExceptionalParabolics

theorem tits_no_five_pair
    (hns : ¬ Group.IsSolvable Atlas1600Group)
    (B : Subgroup Atlas1600Group) (S : Sylow 2 Atlas1600Group)
    (hB : XiOddQuotient 5 B)
    (hperm : (B : Set Atlas1600Group) * (S : Set Atlas1600Group) =
      (S : Set Atlas1600Group) * (B : Set Atlas1600Group)) : False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨M,hM,_,_,hSM,h25⟩ := exists_oddIndex_maximal_with_prime_square B S hB.isPGroup
    (by decide : 5 ≠ 2) (prime_square_dvd_complement hB) hperm hns
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Atlas1600Group S atlas1600SylowTwo
  let e := MulAut.conj g
  let N := M.map e.toMonoidHom
  have hN : N ≠ ⊤ := by
    intro hN
    apply hM.ne_top
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective e.toMonoidHom e.surjective]
    exact hN
  have hSN : atlas1600SylowTwoSubgroup ≤ N := by
    have hh : (S : Subgroup Atlas1600Group).map e.toMonoidHom = atlas1600SylowTwoSubgroup := by
      change ((g • S : Sylow 2 Atlas1600Group) : Subgroup Atlas1600Group) = _
      rw [hg,atlas1600SylowTwo_coe]
    rw [← hh]
    exact map_mono hSM
  have hd : 25 ∣ Nat.card N := by
    rw [show Nat.card N = Nat.card M from card_map_of_injective e.injective]
    exact h25
  rcases Tits.ConverseLocalCoverage.le_first_or_second N hN hSN with h | h
  · have hh := hd.trans (card_dvd_of_le h)
    rw [first_card] at hh
    norm_num at hh
  · have hh := hd.trans (card_dvd_of_le h)
    rw [second_card] at hh
    norm_num at hh

variable {κ : GroupClass} {J : Type*} [Group J] [Finite J] {D B : Subgroup J} {S : Sylow 2 J}

theorem not_tits [Group.IsPerfect D]
    (hA : OddCartan.AmbientInput κ D B S 5)
    (hB : SourceTransport.PairAction 5 (S : Subgroup J) B)
    (e : D ≃* Tits.ParrottGroup) : False := by
  let f := e.trans parrottFiniteImageEquiv
  let : D.Normal := hA.normal
  let : IsSimpleGroup D := hA.simple
  let : IsSimpleGroup Atlas1600Group := f.symm.isSimpleGroup
  let : Group.IsPerfect Atlas1600Group := Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  obtain ⟨U,_,hU,hperm⟩ := exists_model_sylow_pair S hA.inside hB.oddComplement hA.permutes f
  exact tits_no_five_pair (Group.IsPerfect.not_isSolvable Atlas1600Group) _ U hU hperm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
