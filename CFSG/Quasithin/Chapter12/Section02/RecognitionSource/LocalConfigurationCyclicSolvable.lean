module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicDefs
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable

/-!
# The solvable minimal-parabolic entry to the odd-subgroup construction

Movement of the original V modulo O₂(H) rules out normality of T in H.
H-star minimality therefore gives an actual minimal parabolic on the carrier
H, with its Sylow subgroup obtained by restricting the original T. Apply the
proved solvable B.6.8(2) theorem to identify the odd-prime residual in the
literal quotient H/O₂(H). Finally the permitted natural-analysis input
supplies an H-star witness, so this quotient is obtained existentially too.

This starts the construction on printed p.802; lifting P and constructing
the TI pair and invariant W remain the 12.2.21--22 source obligations.
Source: Aschbacher--Smith, 12.2.19--22, using B.6.8(2), pp.113--114,802.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G} {d : ℕ}

theorem chosen_hstar_intrinsic_minimalParabolic (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hn : ¬ ((T : Subgroup G).subgroupOf H).Normal := by
    intro hN
    have hNT : H ≤ normalizer (T : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hTH).mp hN
    exact A.hstar_movement H hH (D.le_sylow.trans
      (le_pCoreIn_of_normalizes T.isPGroup' hTH hNT))
  have hp := Chapter3.HStar.minimalParabolic T D.sylow_normalizes_component hH (Or.inr hn)
  obtain ⟨hTB, hBH, _⟩ :=
    Chapter3.HStar.unique_maximal T D.sylow_normalizes_component hH
  exact (ChapterB.intrinsic_minimalParabolic T H
    (H ⊓ normalizer (L : Set G)) hp hTB hBH).1

/-- The odd-prime residual on the actual quotient H/O₂(H), before selecting
and lifting the Sylow p-subgroup. -/
theorem chosen_hstar_solvable_quotient (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      pResidual 2 (H ⧸ pCore 2 H) = pCore p (H ⧸ pCore 2 H) ∧
      IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ pCore p (H ⧸ pCore 2 H)) := by
  obtain ⟨p, hp, ho, hr, hq, _⟩ := ChapterB.minimalParabolic_solvable_structure
    (T.subtype hH.1.1.2) (chosen_hstar_intrinsic_minimalParabolic D A hH)
    (A.hstar_solvable H hH)
  exact ⟨p, hp, ho, hr, hq⟩

theorem exists_chosen_solvable_odd_quotient (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) :
    ∃ (H : Subgroup G) (p : ℕ),
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      Group.IsSolvable H ∧ p.Prime ∧ Odd p ∧
      pResidual 2 (H ⧸ pCore 2 H) = pCore p (H ⧸ pCore 2 H) ∧
      IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ pCore p (H ⧸ pCore 2 H)) := by
  obtain ⟨H, hH⟩ := A.exists_hstar
  obtain ⟨p, hp, ho, hr, hq⟩ := chosen_hstar_solvable_quotient D A hH
  exact ⟨H, p, hH, A.hstar_solvable H hH, hp, ho, hr, hq⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

