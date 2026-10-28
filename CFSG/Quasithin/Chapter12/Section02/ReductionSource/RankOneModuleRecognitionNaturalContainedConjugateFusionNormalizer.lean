module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionFrattini
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Normalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedReduction

/-!
# The source central-line Sylow normalizer

The subgroup S=C_T(Z_S) is normalized by T and contains T∩L.
Consequently T is already Sylow in N_M(S). The proved original 4.3.1
normalizer theorem applies with this literal T, using the existing
uniqueness over LT. This proves 6.1.9(2) for the original Chapter 12 layer
without the unfinished stronger uniqueness over L in 4.3.2.

Frattini then supplies the exact normalizer factorization used by 6.1.11
under C_G(Z_S)≤M. These two source conclusions have no additional geometry,
normalizer, uniqueness or fusion callbacks.
Source: Aschbacher--Smith, 4.3.1, printed p.613, and 6.1.9, p.669.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The source S is T-normal, so 4.3.1 uses uniqueness over LT, without
the stronger unfinished uniqueness over L in 4.3.2. -/
theorem source_central_line_S_normalizer_le
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n) :
    normalizer (((T : Subgroup G) ⊓ centralizer
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := by
  let Z := Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)
  let S := (T : Subgroup G) ⊓ centralizer (Z : Set G)
  let M := normalizer (L : Set G)
  let N := M ⊓ normalizer (S : Set G)
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (h611.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer Z))).trans
        inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ N := le_inf D.sylow_normalizes_component hTS
  let P : Sylow 2 N := T.subtype hTN
  have hP : (P : Subgroup N).map N.subtype = (T : Subgroup G) := by
    change ((T : Subgroup G).subgroupOf N).map N.subtype = _
    exact map_subgroupOf_eq_of_le hTN
  obtain ⟨Q, hQ⟩ := Chapter4.Section03.RankOneUniqueness.exists_sylow_component D
  have hQS : (Q : Subgroup L).map L.subtype ≤ S := by
    rw [hQ]
    exact le_inf inf_le_left (le_centralizer_iff.mpr inf_le_right)
  apply Chapter4.Section03.RankOneUniqueness.normalizer_le_of_uniqueness_over_local_sylow
    D h h611.quotient_model S (T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans D.sylow_normalizes_component) Q hQS P
  rw [hP]
  exact Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h

/-- The needed 6.1.9(5) factorization is now established on the actual
contained Chapter 12 source, with no normalizer or fusion callback. -/
theorem source_central_line_normalizer_factorization
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G)) :
    CentralLineNormalizerFactorization (normalizer (L : Set G))
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) :=
  centralLineNormalizerFactorization_of_S_normalizer h611 hI
    (source_central_line_S_normalizer_le D h h611)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
