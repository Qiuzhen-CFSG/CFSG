module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Setup

/-!
# The Sylow marking of the Fitting commutator's actor

The actual image of T_v is Sylow in G_v*, and normalizes J(T_v)*.
Together with the full conjugate-span description of J(G_v)* these are
the markings needed to apply an FF structural argument. In particular
the acting subgroup is not replaced by a Sylow subgroup of J(G_v)*.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.6 and the paragraph after 13.6.13, printed pp.928–929.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter
variable {G : Type*} [Group G]

private theorem normalizes_thompson (S : Subgroup G) :
    S ≤ normalizer (Stellmacher.elementaryAbelianMaxJ S : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq]
  have hS : S.map (MulAut.conj x).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hx)
  have hJ := Stellmacher.elementaryAbelianMaxJ_map_equiv (MulAut.conj x) S
  rw [hS] at hJ
  exact hJ.symm

variable [Finite G]

/-- All Sylow, normalization and generation markings on the literal star
subgroups, deduced from the earlier Sylow conclusion for T_v. -/
theorem exists_starSylow_marking (T : Subgroup G) (z v : G)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) :
    ∃ S : Sylow 2 (Gstar z v),
      (S : Subgroup (Gstar z v)) = starImage z v (Tv T v) ∧
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ≤ S ∧
      (S : Subgroup (Gstar z v)) ≤ normalizer
        (starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)) : Set _) ∧
      JGstar z v = conjugateSpanBy
        (starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))) ⊤ := by
  obtain ⟨P, hP⟩ := hSyl
  have hT : (P : Subgroup (Gv v)).map (starMk z v) = starImage z v (Tv T v) := by
    rw [starImage, ← hP]
    change _ = (((P : Subgroup (Gv v)).map (Gv v).subtype).comap
      (Gv v).subtype).map (starMk z v)
    rw [comap_map_eq_self_of_injective (Gv v).subtype_injective]
  have hJ := starImage_intrinsic_thompson z v (P : Subgroup (Gv v)) (Tv T v) hP
  refine ⟨P.mapSurjective (starMk_surjective z v), ?_, ?_, ?_,
    JGstar_eq_conjugateSpan T z v ⟨P, hP⟩⟩
  · exact hT
  · rw [← hJ]
    exact map_mono (sSup_le fun A hA => hA.1)
  · change (P : Subgroup (Gv v)).map (starMk z v) ≤ _
    rw [← hJ]
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [← map_commutator]
    have hn := normalizes_thompson (P : Subgroup (Gv v))
    have hc : ⁅Stellmacher.elementaryAbelianMaxJ (P : Subgroup (Gv v)),
        (P : Subgroup (Gv v))⁆ ≤ Stellmacher.elementaryAbelianMaxJ (P : Subgroup (Gv v)) :=
      le_normalizer_iff_commutator_le_left.mp hn
    exact map_mono hc

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter
