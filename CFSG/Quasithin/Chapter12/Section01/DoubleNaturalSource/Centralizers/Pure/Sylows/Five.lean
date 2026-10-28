module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Marking
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# Ambient pure-point Sylows from the earlier weak-closure conclusion

Positive w places W₀ in C_T(W), hence in C_T(w). E.3.15 makes N_G(C_T(w))
normalize W₀, and E.3.34 puts this normalizer in M. The finite two-group
normalizer condition now promotes the relative Sylow to C_G(w).
For n = 5 this uses precisely the earlier 12.1.3 premise; it does not assert
or assume the later dimension-four weak-closure conclusion.
Source: Aschbacher--Smith 12.1.5(1), printed p.791.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Positive weak closure controls the full ambient normalizer of C_T(w). -/
theorem doubleNatural_point_normalizer_of_globalW_pos_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hw : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T)
    (w : componentOrbit V (T : Subgroup G)) :
    normalizer (((T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  let U := (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G)
  have hQU : (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ≤ U :=
    inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr w.property))
  have he := ChapterE.SourceContainment.weakClosure_eq_of_centralizer_le T
    (show IsPGroup 2 U from T.2.to_inf_left) hQU hw
  have hn := ChapterE.normalizer_le_weakClosure_normalizer
    (componentOrbit V (T : Subgroup G)) U 0
  rw [← he] at hn
  exact hn.trans (ChapterE.SourceContainment.normalizer_weakClosure_zero_le
    (D.doubledOrbit_E322 h) hw (D.doubledOrbit_centralizer_unique h))

/-- The actual fixed-line T₁ is Sylow in the full point centralizer whenever
positive weak closure is supplied by an earlier source theorem. -/
theorem doubleNatural_marked_pure_sylow_of_globalW_pos_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      w ≠ 1 → ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) =
        (T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G))
        (centralizer ({(w : G)} : Set G)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  have hr := D.doubleNatural_relative_pure_sylow_of_many h hmany B S w hw hp hfix
  obtain ⟨hU, hUC, hmax⟩ := Chapter1.isSylowIn_iff.mp hr
  have hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G))
      (centralizer ({(w : G)} : Set G)) := by
    apply Chapter1.isSylowIn_iff.mpr
    refine ⟨hU, inf_le_right, ?_⟩
    apply prime_overgroup_eq_of_normalizer_control _ _ (normalizer (L : Set G))
      (D.doubleNatural_point_normalizer_of_globalW_pos_of_many h hmany hW w)
    intro U hU hTU hUC hUM
    exact hmax U hU hTU (le_inf hUM hUC)
  exact ⟨he, he ▸ hs⟩

/-- The dimension-five branch consumes only the allowed earlier 12.1.3 premise. -/
theorem doubleNatural_five_marked_pure_sylow_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      w ≠ 1 → ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) =
        (T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G))
        (centralizer ({(w : G)} : Set G)) :=
  D.doubleNatural_marked_pure_sylow_of_globalW_pos_of_many h hmany B hW

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
