module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Terminal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.PlaneCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.ThompsonNormalizer
public import Theory.GroupTheory.ElementaryThompsonElementaryCore

/-!
# Thompson-core and normalizer assembly for the solvable branch

The original chamber places T inside the literal third vertex H₀. The
marked plane-core calculation proves that O₂(H₀) is elementary of order
64; relative normality of J(T), supplied by 13.4.7(1ii), now gives
J(T)=O₂(H₀). The 13.4.7(2) overgroup supplement gives N_G(J(T))≤E.

The final application consequently no longer assumes commutativity of
J(T) or containment of its ambient normalizer. Its representative premise
refers to the actual ambient image of O₂(H₀), and the existing Burnside and
characteristic-two arguments supply ambient fusion and centralizers.

This is a conditional step of Aschbacher–Smith 13.4.9, pp.906–907.
Construction of the marked chamber from 13.4.8 and the intrinsic four-class
and commuting-product calculations remain necessary. The earlier 13.4.7
normality and universal product formula are retained explicitly.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The chamber equality retains the original ambient Sylow subgroup. -/
theorem original_sylow_le_plane (D : ChosenModule T L V)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀) : (T : Subgroup G) ≤ H₀ := by
  let E := generated (normalizer (L : Set G)) z H₀
  have hTE : (T : Subgroup G) ≤ E :=
    D.sylow_normalizes_component.trans (first_le_generated _ _ _)
  have h := C.system.T_le 2
  rw [C.chamber, C.third] at h
  intro t ht
  exact h (show (⟨t, hTE ht⟩ : E) ∈ (T : Subgroup G).subgroupOf E from ht)

/-- The original elementary Thompson subgroup is the actual third-vertex core. -/
theorem thompson_eq_plane_core (D : ChosenModule T L V)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (hnormal : H₀ ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    elementaryAbelianMaxJ (T : Subgroup G) = H₀.pCoreIn 2 :=
  elementaryAbelianMaxJ_eq_pCoreIn T H₀ (original_sylow_le_plane D z H₀ C) hnormal
    (original_plane_core_elementary (generated (normalizer (L : Set G)) z H₀) H₀
      le_sup_right C.system C.third)

/-- The commutativity needed by Burnside fusion is a conclusion. -/
theorem original_thompson_elementary (D : ChosenModule T L V)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (hnormal : H₀ ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    IsElementaryAbelian 2 (elementaryAbelianMaxJ (T : Subgroup G)) := by
  rw [thompson_eq_plane_core D z H₀ C hnormal]
  exact original_plane_core_elementary (generated (normalizer (L : Set G)) z H₀) H₀
    le_sup_right C.system C.third

/-- The same Thompson subgroup has order 64. -/
theorem original_thompson_card (D : ChosenModule T L V)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (hnormal : H₀ ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    Nat.card (elementaryAbelianMaxJ (T : Subgroup G)) = 64 := by
  rw [thompson_eq_plane_core D z H₀ C hnormal]
  exact original_plane_core_card (generated (normalizer (L : Set G)) z H₀) H₀
    le_sup_right C.system C.third

open scoped Pointwise in
/-- Apply the fusion endpoint after discharging its Thompson and normalizer inputs. -/
theorem isPSp_of_source_thompson_data
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (hnormal : H₀ ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (supplement : ∀ X : Subgroup G, X ∈ Chapter1.HOver G (H₀ : Set G) →
      (X : Set G) = (H₀ : Set G) *
        (X ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H₀ : Set G) : Subgroup G))
    (hr : ∀ a ∈ generated (normalizer (L : Set G)) z H₀,
      BenderSuzuki.PFAppendixIII.IsInvolution a →
      ∃ c ∈ generated (normalizer (L : Set G)) z H₀,
        MulAut.conj c a ∈ H₀.pCoreIn 2)
    (hpair : ∀ d ∈ V ⊓ centralizer (L : Set G), d ≠ 1 →
      ∀ e ∈ generated (normalizer (L : Set G)) z H₀,
      (∃ c ∈ generated (normalizer (L : Set G)) z H₀, MulAut.conj c d = e) →
      Commute d e → e ≠ d →
      ∃ c ∈ generated (normalizer (L : Set G)) z H₀,
        (T : Subgroup G) ≤ centralizer ({MulAut.conj c (d * e)} : Set G)) :
    ClassicalGroup.IsPSp G 3 2 := by
  let := original_thompson_elementary D z H₀ C hnormal
  apply isPSp_of_thompson_local_data h₀ h structural D m z H₀ C inferInstance
    (thompson_normalizer_le_generated h structural D m z H₀ hnormal supplement) _ hpair
  intro a ha hai
  obtain ⟨c, hc, hac⟩ := hr a ha hai
  exact ⟨c, hc, (thompson_eq_plane_core D z H₀ C hnormal).symm ▸ hac⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
