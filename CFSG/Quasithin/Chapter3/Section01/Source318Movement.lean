module

public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ChapterThreeSylow
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple

/-!
# Thompson movement from a noncentral Sylow omega-center

Under the original qrc hypotheses and uniqueness, a comparison subgroup H
which moves the Sylow omega-center forces J(T) to move V. Otherwise the
complete E.2.3 analysis makes O₂(M₀) Sylow in O²(H)O₂(M₀), while the
common-normal theorem and uniqueness exclude that Sylow conclusion.

This is the noncentral implication of 3.1.8(3), using the proved 3.1.7
residual-Sylow argument on the literal omega-center orbit. No independent
classification or common-normal premise remains.
Source: Aschbacher--Smith, Theorems 3.1.1 and 3.1.8(3), and Lemma 3.1.7,
combined manuscript of 1 March 2004, printed pp.571--576.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The noncentral omega-center branch of the original Thompson alternative. -/
theorem QrcHypotheses.thompson_moves_of_noncentral_omega
    (h : QrcHypotheses T M M₀ H V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hV : V ≠ ⊥)
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
  intro hJ
  have hR : M₀.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hV (bot_unique ((h.toQRCConfiguration (h.no_common_normal hu)).module_le_core.trans_eq he))
  exact h.not_residual_sylow (source_common_normal_knownSimple hG T) hR hu
    (h.residual_sylow_source hG hM hu hJ hZ)

end CFSG.Quasithin.Chapter3
