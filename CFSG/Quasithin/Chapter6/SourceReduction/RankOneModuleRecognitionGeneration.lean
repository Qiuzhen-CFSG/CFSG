module

public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple

/-!
# Attained generation in the small rank-one branch

Every actual member of H*(T,M) has a nontrivial two-core. Its order is
therefore even, and the simple QTKE hypotheses make it an SQTK group.
The KnownSimple generation theorem then gives a positive, attained
generation parameter. In particular, the bound at most one used in the
Chapter 12 case split gives the equality required by Hypothesis 6.1.1.

Source: Aschbacher--Smith, Definition 3.0.1, Lemma 3.1.2 and Hypothesis
6.1.1(2), printed pp.571--572 and 663; E.1.11--12, pp.212--214.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M H : Subgroup G}

/-- Positivity and attainment concern the actual H* member, using its
nontrivial two-core and inherited SQTK structure. -/
theorem hstar_generation_spec
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    0 < ChapterE.generationParameter H ∧
      ChapterE.IsEGenerated (ChapterE.generationParameter H) H := by
  have hcore : H.pCoreIn 2 ≠ ⊥ := hH.1.1.1
  let : Nontrivial (H.pCoreIn 2) := (nontrivial_iff_ne_bot _).mpr hcore
  obtain ⟨n, hn, hc⟩ := (isPGroup_pCoreIn 2 H).nontrivial_iff_card.mp
    (inferInstance : Nontrivial (H.pCoreIn 2))
  have heven : ¬ Odd (Nat.card H) := by
    apply Nat.not_odd_iff_even.mpr
    apply even_iff_two_dvd.mpr
    apply dvd_trans _ (card_dvd_of_le (H.pCoreIn_le 2))
    rw [hc]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  exact ChapterE.source_generation_spec_knownSimple
    (Chapter3.sqtk_of_mem_H hG hH.1.1.1) (T.subtype hH.1.1.2) heven

/-- The small numerical branch supplies the literal equality in 6.1.1(2).
No positivity property of an unattained natural infimum is used. -/
theorem hstar_generation_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hsmall : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      ChapterE.generationParameter H ≤ 1) :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      ChapterE.generationParameter H = 1 := by
  intro H hH
  exact Nat.le_antisymm (hsmall H hH) (hstar_generation_spec hG hH).1

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
