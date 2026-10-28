module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.SpecificGroups.Alternating.SixSectionNormalizerBound
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.Quasithin.CoprimeRank

/-!
# Alternating-six sections and small Sylow-normalizer index in binary Sp₄

A perfect subgroup with three-rank at least two cannot normalize a nontrivial
two-subgroup: the actual two-local parabolic cover would embed it in a
perfect subgroup of three-rank at most one. An A₆ two-core quotient supplies
that rank. The faithful normalizer bound then makes a Sylow meeting the
normalizer in index at most four have order at most128. Its actual order
q^4, for q at least four, contradicts this bound.

The consumer maps the original L_v into K_v/O₂(K_v), retaining its perfect
image, A₆ section and actual index-four Sylow geometry. No full-Sylow
normalization or model-family tag is substituted.
Source: Aschbacher--Smith, 12.6.17, printed p.827, with A.2.10--11, p.35,
and the defining-characteristic two-local geometry, pp.3--4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A perfect subgroup of odd-prime rank at least two normalizes no nontrivial
binary subgroup in Sp₄: the two-local parabolic cover would force rank at most one. -/
theorem two_subgroup_eq_bot_of_perfect_odd_rank_two
    (A R : Subgroup (Sp F)) [Group.IsPerfect A]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p A)
    (hp : IsPGroup 2 R) (hn : A ≤ normalizer (R : Set (Sp F))) : R = ⊥ := by
  by_contra hR
  obtain ⟨g,hg⟩ := twoLocal_parabolic_cover_of_charTwo
    (normalizer (R : Set _)) ⟨R,hR,hp,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp A.subtype
  have hj : j.range ≤ (normalizer (R : Set _)).map (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨a,rfl⟩
    exact mem_map_of_mem _ (hn a.property)
  exact no_perfect_odd_rank_two_in_parabolic ho hr j
    ((MulAut.conj g).injective.comp A.subtype_injective) (hg.imp hj.trans hj.trans)
end Theory.SpecificGroups.SymplecticFour

namespace Theory.SpecificGroups.SymplecticFour
open Subgroup Theory.GroupTheory
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem no_six_section_of_small_sylow_normalizer_index {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (A : Subgroup (Sp F)) [Group.IsPerfect A]
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 (Sp F)) (hi : (normalizer (A : Set (Sp F))).relIndex S ≤ 4) : False := by
  have hr : 2 ≤ primeRank 3 A := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 A) pCore_isPGroup,
      primeRank_equiv 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hb := Theory.SpecificGroups.Alternating.six_section_sylow_card_le A e
    (fun R hp hR => two_subgroup_eq_bot_of_perfect_odd_rank_two A R (by decide : Odd 3) hr hp hR)
    (S : Subgroup (Sp F)) S.isPGroup' hi
  have hc : Nat.card S = (Nat.card F)^4 := by
    rw [Nat.card_congr (S.equiv (unipotentSylow hF (by omega))).toEquiv]
    exact card_unipotent
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  have hh := Nat.pow_le_pow_left hq 4
  rw [hc] at hb
  norm_num at hh
  omega
end Theory.SpecificGroups.SymplecticFour
