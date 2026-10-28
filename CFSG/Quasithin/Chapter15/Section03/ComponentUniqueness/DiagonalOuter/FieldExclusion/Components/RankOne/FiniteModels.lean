module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.FiniteModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.Automorphisms
public import CFSG.Quasithin.ChapterA.Section02.Statements

/-!
# Alternating and sporadic cases of the rank-one automorphism calculation

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137 (PDF p.1154),
and the exact Theorem C list on printed p.33 (PDF p.44).

Two disjoint three-cycles reduce the nonabelian simple alternating case to A₅;
its actual outer automorphism group is a two-group. The five Mathieu groups,
J₂, J₄, He and Ru have three-rank at least two, by actual elementary subgroups
or noncyclic three-subgroups. The remaining J₁ and HS branches use the proved
structure of their actual outer automorphism groups. Since a rank-one Sylow
three-subgroup is cyclic, every cubic automorphism subgroup is then cyclic.

`cubic_alternating` is re-exported from `Basic`. `cubic_sporadic` handles every
constructor of the exact source predicate, including J₁ and excluding J₃.
There are no additional model or automorphism premises. These supply the finite
branches to the parent rank-one exclusion; this module does not import that
parent and does not assert the independent Lie-type branches.
-/

public section

open Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne.FiniteModels
universe u v
variable {S : Type u} [Group S] [Finite S]

private theorem rank_one_impossible {T : Type v} [Group T] [Finite T]
    (e : S ≃* T) (hT : 2 ≤ primeRank 3 T) (hr : primeRank 3 S = 1) : False := by
  rw [← primeRank_equiv 3 e, hr] at hT
  omega

/-- Every rank-one nonabelian simple model in Theorem C(5) has abelian
subgroups of exponent dividing three in its actual automorphism group. -/
theorem cubic_sporadic [IsSimpleGroup S]
    (hna : ¬ IsMulCommutative S) (hr : primeRank 3 S = 1)
    (h : ChapterA.Section02.IsTheoremCSporadicModel S) : CubicAutomorphismsAbelian S := by
  rcases h with h | h
  · obtain ⟨name, hn, ⟨e⟩⟩ := h
    let : Finite name.Carrier := Finite.of_injective e.symm e.symm.injective
    cases name with
    | m11 => exact (rank_one_impossible e m11_rank_ge_two hr).elim
    | m12 => exact (rank_one_impossible e m12_rank_ge_two hr).elim
    | m22 => exact (rank_one_impossible e m22_rank_ge_two hr).elim
    | m23 => exact (rank_one_impossible e m23_rank_ge_two hr).elim
    | m24 => exact (rank_one_impossible e m24_rank_ge_two hr).elim
    | j2 => exact (rank_one_impossible e j2_rank_ge_two hr).elim
    | j3 => exact (hn rfl).elim
    | j4 => exact (rank_one_impossible e j4_rank_ge_two hr).elim
    | hs => exact cubic_hs hna hr e
    | he => exact (rank_one_impossible e held_rank_ge_two hr).elim
    | ru => exact (rank_one_impossible e ru_rank_ge_two hr).elim
  · obtain ⟨e⟩ := h
    exact cubic_j1 hna hr e

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne.FiniteModels
