module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import Stellmacher.OmegaOneCenterMap
public import Stellmacher.ElementaryAbelianMaxOrder
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The ambient Thompson normalizer from the source overgroup supplement

The original fixed line lies in Ω₁Z(T). Therefore the centralizer of
V₀=⟨(Ω₁Z(T))ᴴ⁰⟩ lies in M=N_G(L). The normalizer N of J(T) has nontrivial
two-core, since J(T) is a nontrivial two-subgroup normal in N. Thus the
13.4.7(2) supplement applies to N as soon as H₀ normalizes J(T):
N=H₀ C_N(V₀) is contained in the original generated group E.

Both relative normality and the universal overgroup product formula are
explicit earlier-source inputs, furnished by 13.4.7(1ii),(2),(4) in the
L₂ branch. The formula uses the literal conjugate span and actual ambient
centralizers; no fusion or normalizer-containment conclusion is assumed.
Source: Aschbacher–Smith 13.4.7, pp.899–903, and 13.4.9, p.906.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The fixed line lies in the center of the original Sylow subgroup. -/
theorem fixed_le_original_omegaCenter
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    V ⊓ centralizer (L : Set G) ≤ omegaOneCenterAmbient (T : Subgroup G) := by
  let := D.elementary
  intro d hd
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨D.le_sylow hd.1, elemPow_eq_one_of_isElementaryAbelian d hd.1, ?_⟩
  intro t ht
  exact (mem_centralizer_iff.mp
    (normalizer_component_le_fixed_centralizer h structural D m
      (D.sylow_normalizes_component ht)) d hd).symm

/-- The actual five-dimensional module forces J(T) to be nontrivial. -/
theorem original_maxJ_ne_bot (D : ChosenModule T L V) (m : CoreMarking D) :
    elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥ := by
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
  have hAV := hA.2.2 V D.le_sylow D.elementary
  rw [m.card_module] at hAV
  intro hbot
  have hAbot : A = ⊥ := le_bot_iff.mp (hbot ▸ le_sSup hA)
  rw [hAbot, card_bot] at hAV
  omega

open scoped Pointwise in
/-- Apply the earlier overgroup supplement to N_G(J(T)), proving its applicability. -/
theorem thompson_normalizer_le_generated
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : G) (H₀ : Subgroup G)
    (hnormal : H₀ ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (supplement : ∀ X : Subgroup G, X ∈ Chapter1.HOver G (H₀ : Set G) →
      (X : Set G) = (H₀ : Set G) *
        (X ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H₀ : Set G) : Subgroup G)) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      generated (normalizer (L : Set G)) z H₀ := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let N := normalizer (J : Set G)
  have hJT : J ≤ T := sSup_le fun _ hA => hA.1
  have hJN : J ≤ N := J.le_normalizer
  have hcore : J ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) hJN le_rfl
  have hN : N ∈ Chapter1.HOver G (H₀ : Set G) := by
    refine ⟨?_, hnormal⟩
    intro hbot
    exact original_maxJ_ne_bot D m (le_bot_iff.mp (hbot ▸ hcore))
  have hcent : centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H₀ : Set G) ≤
      normalizer (L : Set G) := by
    rw [← fixed_centralizer_eq_normalizer h structural D m]
    exact centralizer_le ((fixed_le_original_omegaCenter h structural D m).trans
      (le_conjugateSpanBy _ _))
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := (supplement N hN).le hx
  exact (generated (normalizer (L : Set G)) z H₀).mul_mem
    ((show H₀ ≤ generated (normalizer (L : Set G)) z H₀ from le_sup_right) ha)
    ((first_le_generated _ _ _) (hcent hc.2))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
