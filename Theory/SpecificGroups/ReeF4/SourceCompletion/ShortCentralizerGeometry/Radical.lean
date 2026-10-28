module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry.Torus
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.CommutatorGeneration.FixedGenerators

/-!
# The full linear radical centralizes the long-root plane

The seven fixed main curves generating the actual linear radical lie in the
replacement section C. The established root commutators show that C centralizes
V. Consequently every radical marker centralizes the same literal plane; this
applies to an extremal short marker without changing its chosen extension.

Source: the natural-module step of Aschbacher--Smith F.4.42, printed p.295
(`refs/quasithin.pdf`); fixed root generation follows GLS3 Table 2.4.
-/

public noncomputable section
open Subgroup
namespace ReeF4.SourceCompletion.ShortCentralizerGeometry
open Parabolics LargeLocalSeeds ElementaryTwoBound
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

/-- The entire fixed linear radical lies in the seven-curve replacement section. -/
theorem radical_le_C (m : ℕ) : radical m .linear ≤ Replacement.C m := by
  have hgen : closure {z | ∃ i : Fin 8, i ≠ 7 ∧
      ∃ t : CoefficientField m, z = rootWord m i t} ≤
      (Replacement.C m).map (toSplitGroup m) := by
    apply (closure_le _).mpr
    rintro z ⟨i, hi, t, rfl⟩
    exact ⟨mainElement m i t, Replacement.mainElement_mem_C m i hi t,
      mainElement_coe m i t⟩
  intro z hz
  have hfix : (canonicalLocalBlockInput m).twist (toSplitGroup m z) = toSplitGroup m z := by
    rw [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply]
    exact reeTwist_toSplitGroup m z
  obtain ⟨u, hu, he⟩ := hgen
    (LinearCommutators.fixed_radical_mem_closure (canonicalLocalBlockInput m)
      (toSplitGroup m z) hz hfix)
  exact toSplitGroup_injective m he ▸ hu

/-- The full radical acts trivially on the actual long-root plane. -/
theorem radical_centralizes_plane (m : ℕ) :
    radical m .linear ≤ centralizer (Replacement.V m : Set (Model m)) :=
  (radical_le_C m).trans (Replacement.CentralizerGeometry.C_centralizes_V m)

/-- Every marker in the linear radical centralizes the same literal plane. -/
theorem plane_le_short_centralizer {m : ℕ} {t : Model m}
    (ht : t ∈ radical m .linear) :
    Replacement.V m ≤ centralizer ({t} : Set (Model m)) := by
  intro v hv
  exact mem_centralizer_singleton_iff.mpr (radical_centralizes_plane m ht v hv)

end ReeF4.SourceCompletion.ShortCentralizerGeometry
