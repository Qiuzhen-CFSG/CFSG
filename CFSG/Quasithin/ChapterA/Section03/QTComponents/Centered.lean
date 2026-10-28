module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.SourceRanks
public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.LocalRankSieve
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.ComponentModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.SimpleException
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.PerfectCenterPrimeRank
public import Theory.Quasithin.ComponentRanks.LocalBounds

/-!
# Centered nonnormal components in quasithin K-groups

A distinct commuting conjugate bounds the component's ordinary odd ranks,
so the proved Theorems A and C give its literal central-quotient model.
The complete covering catalogue forces a nontrivial center to have order
three. Cubic-intersection local rank and the complete three-cover sieve
then identify the original component as an odd-degree binary SU₃ group.
Its central quotient retains the matching PSU₃ marking.

Source: Aschbacher–Smith A.1.34(3), A.3.8(1–2), pp.29–30,45–46.
We retain every odd binary unitary exponent; no claim of exponent three
or of the full centerless component shortlist is made here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.QTComponents
open Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The original central quotient has the complete Theorem C model. -/
theorem nonnormal_centralQuotient_model
    (hG : IsQuasithin G) (hκ : IsKGroup KnownSimple.IsKnownSimple G)
    (K : Subgroup G) (hK : IsComponent G K) (hn : ¬ K.Normal) :
    LocalModels.TheoremCModel (K ⧸ center K) := by
  classical
  have hN : normalizer (K : Set G) ≠ ⊤ :=
    fun he => hn (normalizer_eq_top_iff.mp he)
  obtain ⟨g,hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hN)
  have hne : K ≠ K.map (MulAut.conj g).toMonoidHom :=
    fun he => hg.2 (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center K))
  have hm := Section02.component_centralQuotient_models_of_ne
    (fun H _ _ _ => Section02.theoremsABC_knownSimple (G := H)) hG hκ
    hK (hK.map_conj g) hne
  exact Section03.SourceComponents.sourceTheoremC_to_local
    (Group.IsPerfect.not_isMulCommutative (K ⧸ center K)) hm.2.2

private theorem not_fitting_eq_generalizedFitting (K : Type*) [Group K] [Finite K]
    [IsQuasisimple K] : fittingSubgroup K ≠ generalizedFitting K := by
  intro he
  have ht : fittingSubgroup K = ⊤ := he.trans generalizedFitting_eq_top_of_quasisimple
  let : Group.IsNilpotent (⊤ : Subgroup K) := ht ▸
    inferInstanceAs (Group.IsNilpotent (fittingSubgroup K))
  let : Group.IsNilpotent K := Group.nilpotent_of_mulEquiv (topEquiv : (⊤ : Subgroup K) ≃* K)
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact Group.IsPerfect.not_isNilpotent K inferInstance

/-- The shared-center alternative yields a literal special unitary model. -/
theorem nonnormal_centered_specialUnitary
    (hG : IsQuasithin G) (hκ : IsKGroup KnownSimple.IsKnownSimple G)
    (hcore : pCore 2 G = ⊥) (K : Subgroup G)
    (hK : IsComponent G K) (hn : ¬ K.Normal) (hz : center K ≠ ⊥) :
    ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ Section02.IsSpecialUnitaryModel K 3 (2 ^ n) := by
  let : IsQuasisimple K := hK.2
  have hm := nonnormal_centralQuotient_model hG hκ K hK hn
  have hc := SQTKStructure.OrdinarySource.ordinary_conclusion_of_model hcore K hK hm
  have hzcard : Nat.card (center K) = 3 := by
    rcases SQTKStructure.NonnormalOuterSource.FourModels.center_card_of_common hc.2 with he | he
    · exact (hz (card_eq_one.mp he)).elim
    · exact he
  have hp : IsPGroup 3 (center K) := IsPGroup.of_card (n := 1) (by simpa using hzcard)
  have hr := two_le_primeRank_of_nontrivial_prime_center (by decide) hp hz
  have hl := hK.local_threeRank_le_one_of_nonnormal hG hn hzcard.le hr
  have hcover : LocalModels.ThreeCoverModel K := by
    cases hc.1 with
    | simple _ hs _ =>
      let := hs
      have hh : center K = ⊥ := (inferInstance : (center K).Normal).eq_bot_or_eq_top.resolve_right
        (fun ht => Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp ht))
      exact (hz hh).elim
    | cover _ _ hm => exact hm
    | natural hh => exact (not_fitting_eq_generalizedFitting K hh.1.symm).elim
    | nilpotent hh => exact (not_fitting_eq_generalizedFitting K hh.1.symm).elim
  exact Section02.OddCenterCovers.unitary_model_of_threeCover_local_rank_le_one hcover hzcard hl

/-- The actual central quotient of a centered nonnormal component is binary PSU₃. -/
theorem nonnormal_centered_projectiveUnitary
    (hG : IsQuasithin G) (hκ : IsKGroup KnownSimple.IsKnownSimple G)
    (hcore : pCore 2 G = ⊥) (K : Subgroup G)
    (hK : IsComponent G K) (hn : ¬ K.Normal) (hz : center K ≠ ⊥) :
    ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ n) := by
  obtain ⟨n,hnn,ho,hm⟩ := nonnormal_centered_specialUnitary hG hκ hcore K hK hn hz
  exact ⟨n,hnn,ho,hm.projectiveModel (by omega)⟩

end CFSG.Quasithin.ChapterA.QTComponents
