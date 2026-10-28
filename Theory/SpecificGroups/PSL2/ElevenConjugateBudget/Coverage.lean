module

public import Theory.SpecificGroups.PSL2.ElevenConjugateBudget.Coverage.Representatives
public import Theory.SpecificGroups.PSL2.ElevenConjugateBudget.Coverage.MixedFourFusion
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.Representation.BinaryOffender.CubicConjugateBound

/-!
# Exhaustive elementary actor coverage for PSL₂(11)

The automorphism two-rank bound reduces every nontrivial elementary
abelian actor to order two or four. The involutions have an inner and
an outer class. Inner four-groups are Sylow in PSL₂(11); mixed four-groups
are fused by the dihedral Sylow groups of order eight in its full
automorphism group. The representatives are precisely the published
matrix quotient elements t, s and the actual diagonal automorphism d.

This proves the coverage premise of the separately established
finite-generation budget. Arbitrary automorphism conjugators are allowed:
the generation transport sends the PSL₂ conjugators c to their images a(c).
The source application is Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.1, pp.8–9, and Aschbacher–Smith K.2, printed p.453.
-/

public section
open Subgroup GorensteinWalter Representation.BinaryOffender
namespace Theory.PSL2.ElevenConjugateBudget
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
open Coverage

private theorem cyclic_coverage (A : Subgroup (MulAut S)) (hA : IsElementaryTwo A)
    (hc : Nat.card A = 2) :
    ∃ (i : Fin 4) (a : MulAut S), A = (actor i).map (MulAut.congr a).toMonoidHom := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
  have hxI : IsInvolution (x : MulAut S) :=
    ⟨fun h => hx (Subtype.ext h), elemPow_eq_one_of_isElementaryAbelian _ x.property⟩
  have hAz : A = zpowers (x : MulAut S) := by
    apply (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr x.property) ?_).symm
    rw [Nat.card_zpowers, hc, orderOf_eq_prime hxI.2 hxI.1]
  rcases involution_classes (x : MulAut S) hxI with ht | hd
  · obtain ⟨a, ha⟩ := isConj_iff.mp ht
    refine ⟨0, a, ?_⟩
    change A = (zpowers (MulAut.conj t)).map (MulAut.congr a).toMonoidHom
    rw [hAz, MonoidHom.map_zpowers]
    exact congrArg zpowers ha.symm
  · obtain ⟨a, ha⟩ := isConj_iff.mp hd
    refine ⟨1, a, ?_⟩
    change A = (zpowers d).map (MulAut.congr a).toMonoidHom
    rw [hAz, MonoidHom.map_zpowers]
    exact congrArg zpowers ha.symm

/-- Every nontrivial elementary abelian subgroup of the actual automorphism
group of PSL₂(11) is an automorphism conjugate of one of the four actors. -/
theorem actor_coverage : ActorCoverage := by
  intro A hA
  have hr : rank A ≤ 2 := rank_le_of_primeRank_le hA
    (primeField_automorphism_two_rank (p := 11) (by decide))
  have hp := hA.rank_pos
  have hr12 : rank A = 1 ∨ rank A = 2 := by omega
  rcases hr12 with hr1 | hr2
  · exact cyclic_coverage A hA (by rw [hA.card_eq_two_pow_rank, hr1]; rfl)
  · have hc : Nat.card A = 4 := by rw [hA.card_eq_two_pow_rank, hr2]; norm_num
    let : IsElementaryAbelian 2 A := hA.2
    let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA.1
    have hK : IsKleinFour A := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
    by_cases hAi : A ≤ Coverage.inner
    · obtain ⟨a, ha⟩ := inner_four_conjugate A hAi hc
      exact ⟨2, a, ha⟩
    · obtain ⟨a, ha⟩ := mixed_four_conjugate Coverage.inner inner_index sylow_dihedral_eight
        inner_sylow_noncyclic outerFour A outerFour_klein hK outerFour_not_le_inner hAi
      exact ⟨3, a, ha⟩

end Theory.PSL2.ElevenConjugateBudget
