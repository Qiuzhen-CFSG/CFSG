module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting.BestOffenderSplitting
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Commutator control for the final clause of B.1.9

For a noncentral minimal best offender A, choose its actual cubic Fᵢ.
The source group Gᵢ=FᵢA centralizes A modulo the normal subgroup F:
Fᵢ lies in F and A is abelian. The other Gⱼ commute with Gᵢ, and the
residual J_P(C_G(F)) centralizes their generated group E. The best-offender
splitting therefore gives [J(G,V),A] ≤ F, and hence [J*,A] ≤ F.

We implement centralizing modulo F through the checked commutator-preimage
subgroup, using the actual ambient normality of F. Together with
F ≤ Z(F(G)), this supplies both premises of the parent's
conclusion_of_decomposition and completes its clause-(5) argument.

Source: Aschbacher–Smith, B.1.9(5), printed p.72 (PDF p.83).
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Every element of J(G,V) centralizes a noncentral minimal offender modulo F. -/
theorem offenderSubgroup_commutator_minimal_le_fittingMoved
    (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hn : ⁅fittingSubgroup G, A⁆ ≠ ⊥) :
    ⁅offenderSubgroup ρ, A⁆ ≤ fittingMoved ρ := by
  have hm : ⁅fittingSubgroup G, A⁆ ∈ minimalMovedFactors ρ := ⟨A, hA, hn, rfl⟩
  obtain ⟨i, hi⟩ := (range_cubicFactor ρ).symm ▸ hm
  have hAf : A ∈ planeOffenders ρ (cubicFactor ρ i) := ⟨hA, hn, hi.symm⟩
  have hAi := offender_le_planeGroup ρ hAf
  have hAE : A ≤ planeGenerated ρ := hAi.trans (le_iSup (fun j => planeGroup ρ (cubicFactor ρ j)) i)
  let D := commutatorPreimage ⊤ A (fittingMoved ρ)
  have hFD : fittingMoved ρ ≤ D := le_commutatorPreimage le_top (commutator_le_left _ _)
  have hAD : A ≤ D := by
    let : IsElementaryAbelian 2 A := hA.1.1.2
    exact le_commutatorPreimage le_top
      ((commutator_self_eq_bot_iff.mpr inferInstance).le.trans bot_le)
  have hED : planeGenerated ρ ≤ D := by
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst j
      rw [planeGroup_eq_local ρ hρ hlocal hAf]
      exact sup_le ((cubicFactor_le ρ i).trans hFD) hAD
    · apply le_commutatorPreimage le_top
      apply (commutator_eq_bot_iff_le_centralizer.mpr ?_).le.trans bot_le
      exact (planeGroups_commute ρ hρ hlocal (cubicFactor_mem ρ j)
        (cubicFactor_mem ρ i) (fun he => hji (cubicFactor_injective ρ he))).trans
          (centralizer_le hAi)
  have hRD : centralizingBestGenerated ρ ≤ D := by
    apply le_commutatorPreimage le_top
    apply (commutator_eq_bot_iff_le_centralizer.mpr ?_).le.trans bot_le
    exact (centralizingBestGenerated_le_centralizer_planeGenerated ρ hρ hlocal).trans
      (centralizer_le hAE)
  have hJD : offenderSubgroup ρ ≤ D := by
    rw [offenderSubgroup_eq_planeGenerated_sup_centralizingBestGenerated ρ hρ hcore hlocal]
    exact sup_le hED hRD
  exact (commutator_mono hJD le_rfl).trans
    (commutator_commutatorPreimage_le ⊤ A (fittingMoved ρ) le_normalizer_of_normal)

/-- The exact commutator-control input of the parent clause-(5) assembly. -/
theorem minimalGenerated_commutator_minimal_le_fittingMoved
    (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hn : ⁅fittingSubgroup G, A⁆ ≠ ⊥) :
    ⁅minimalGenerated ρ, A⁆ ≤ fittingMoved ρ :=
  (commutator_mono (minimalGenerated_le ρ) le_rfl).trans
    (offenderSubgroup_commutator_minimal_le_fittingMoved ρ hρ hcore hlocal hA hn)

end CFSG.Quasithin.ChapterB.FittingStructure
