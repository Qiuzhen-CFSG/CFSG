module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ActionImage
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.Offenders

/-!
# The chosen-orbit applications of the offender reduction

Under failure of the desired bound, the actual E.3.22 orbit supplies a
conjugate attaining w = 1 or w = 2. The first stage also applies the source
pure-intersection premise to its original natural summand. The resulting
configurations retain the literal conjugate, action image, and dual cores.
The separate H.9 geometric contradictions are still required.

Source: Aschbacher--Smith, 12.1.8 and 12.1.10, pp.792--794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
include h D

/-- The literal first-stage offender and its vanishing pure intersection. -/
theorem doubled_first_configuration_of_many
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    B.PureIntersectionCentralizes →
    0 < globalW (componentOrbit V (T : Subgroup G)) T →
    (n : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    ¬ 1 < globalW (componentOrbit V (T : Subgroup G)) T →
    ∃ g : G,
      IsWOffenderAt (componentOrbit V (T : Subgroup G)) T g ∧
      globalW (componentOrbit V (T : Subgroup G)) T = 1 ∧
      ConjugateConfiguration (componentOrbit V (T : Subgroup G)) g 1 n ∧
      B.naturalSpace ⊓ subgroupSpace (componentOrbit V (T : Subgroup G))
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom) = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro hp hw hr hf
  have hn : 1 < n := by rcases B.degree with rfl | rfl <;> decide
  obtain ⟨g, hg, he, hc⟩ := exists_configuration (D.doubledOrbit_E322 h)
    (j := 1) (r := n) (by decide) hw hf hn hr
  exact ⟨g, hg, he, hc, B.natural_intersection_eq_bot hp g hg.1⟩

/-- The actual E.3.32 configuration used by the second-stage H.9 argument. -/
theorem doubled_second_configuration_of_many
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    1 < globalW (componentOrbit V (T : Subgroup G)) T →
    ((n + 2 : ℕ) : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    ¬ 2 < globalW (componentOrbit V (T : Subgroup G)) T →
    ∃ g : G,
      IsWOffenderAt (componentOrbit V (T : Subgroup G)) T g ∧
      globalW (componentOrbit V (T : Subgroup G)) T = 2 ∧
      ConjugateConfiguration (componentOrbit V (T : Subgroup G)) g 2 (n + 2) := by
  let := D.doubledOrbit_elementary h
  intro hw hr hf
  have hn : 2 < n + 2 := by rcases B.degree with rfl | rfl <;> decide
  exact exists_configuration (D.doubledOrbit_E322 h)
    (j := 2) (r := n + 2) (by decide) hw hf hn hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
