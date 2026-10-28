module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentPreparation
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalSelection

/-!
# TerminalComponentPreparation at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentPreparation`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem omega_commutator_ne_bot_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ⁅P.Z, P.K⁆ ≠ ⊥ := by
  intro he
  apply P.residual_escape_at structural
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
    (omega_center_centralizer_le_at S D structural)

include P in

theorem many_maximal_overgroups_at :
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.hypothesis.simpleQTKE T S.hypothesis.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    have he : componentOrbit L (T : Subgroup G) = L :=
      S.chosen.localOrbit_eq
    simpa only [he] using hu.normalizer_maximal
  obtain ⟨N, hN, hTN, hn⟩ := P.exists_outside_maximal
  apply Set.one_lt_ncard_iff_nontrivial_and_finite.mpr
  exact ⟨⟨N, ⟨hN, hTN⟩, normalizer (L : Set G),
    ⟨hm, S.chosen.sylow_normalizes_component⟩, fun he => hn he.le⟩, Set.toFinite _⟩

theorem exists_moving_hstar_of_maximal_at
    (hmax : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    ∃ H₁ ∈ Chapter3.HStar (T : Subgroup G) (normalizer (P.K : Set G)),
      ¬ H₁ ≤ P.pointCentralizer ∧ ⁅P.Z, H₁⁆ ≠ ⊥ := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.hypothesis.simpleQTKE T hmax
  have horbit : componentOrbit P.K (T : Subgroup G) = P.K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      P.sylow_normalizes_residual) (le_componentOrbit _ _)
  have hm : IsMaximalTwoLocal (normalizer (P.K : Set G)) := by
    simpa only [horbit] using hu.normalizer_maximal
  obtain ⟨H₁, hH₁⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T P.many_maximal_overgroups_at _ hm
      P.sylow_normalizes_residual)
  have hn : ¬ H₁ ≤ P.pointCentralizer :=
    fun hh => hH₁.1.2 (hh.trans (P.pointCentralizer_normalizes_of_maximal hmax))
  refine ⟨H₁, hH₁, hn, ?_⟩
  intro he
  exact hn ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
    (centralizer_le (Set.singleton_subset_iff.mpr P.central)))

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

