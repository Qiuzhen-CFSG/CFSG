module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ModelGeometry
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment

/-!
# The terminal doubled-orbit contradiction under the multiple-overgroup guard

Choose the actual outside H* using the ambient guard. Its Sylow subgroup
is the restriction of T. The bounds w > 2 and r ≥ n+2, and the source
calculation n(H) = 2, give precisely the strict inequality in E.3.35.
The normalizer identity and uniqueness are supplied for the original W.

This is conditional terminal assembly: the weak-closure bound and
generation calculation must still be proved from the doubled branch.
The C_T(W) core identification is proved by the preceding source theorem.
This does not claim the unconditional 12.1.11 theorem.
Source: Aschbacher--Smith, combined manuscript, p.794, used at p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The final E.3.35 argument with its genuine unproved source inputs displayed. -/
theorem doubleNatural_excluded_of_many_of_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (2 : ℕ∞) < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T)
    (hr : ((n + 2 : ℕ) : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)))
    (hgen : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      ChapterE.generationParameter H = 2) : False := by
  let W := componentOrbit V (T : Subgroup G)
  let := D.doubledOrbit_elementary h
  obtain ⟨H, hH⟩ := D.doubledOrbit_outside_of_many h hmany
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have htwo : (2 : ℕ∞) < ChapterE.globalR W := by
    have hn : 2 < n + 2 := by rcases B.degree with rfl | rfl <;> omega
    exact lt_of_lt_of_le (by exact_mod_cast hn) hr
  have hn : (ChapterE.generationParameter H : ℕ∞) <
      min (ChapterE.globalW W T) (ChapterE.globalR W) := by
    rw [hgen H hH]
    exact lt_min hw htwo
  apply hH.1.2
  apply ChapterE.SourceContainment.le_of_generationParameter_pos
    (D.doubledOrbit_E322 h) (T.subtype hTH) (D.doubledOrbit_centralizer_unique h)
  · exact inf_le_right.trans ((centralizer_le_normalizer (W : Set G)).trans
      (D.doubledOrbit_normalizer_eq h B.orbit_eq).le)
  · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (W : Set G) ≤ T)
  · rw [hgen H hH]
    decide
  · exact hn

/-- The chosen-orbit application of the geometric and numerical source
inputs. Every surviving premise is an earlier 12.1 obligation. -/
theorem doubleNatural_excluded_of_many_of_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (2 : ℕ∞) < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T)
    (hgen : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      ChapterE.generationParameter H = 2) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers → B.OddFixedSpaces → False := by
  let := D.doubledOrbit_elementary h
  intro hcentral hfixed
  exact doubleNatural_excluded_of_many_of_parameters h D hmany B hw
    (B.globalR_ge_add_two (D.doubledOrbit_normalizer_eq h B.orbit_eq) hcentral hfixed) hgen

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
