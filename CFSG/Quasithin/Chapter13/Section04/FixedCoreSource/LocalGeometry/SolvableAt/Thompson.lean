module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Geometry.ThompsonNormalizer
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Terminal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Thompson

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Terminal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.PlaneCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.ThompsonNormalizer
public import Theory.GroupTheory.ElementaryThompsonElementaryCore

/-!
# Thompson-core and normalizer assembly for the solvable branch: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Thompson` proof for the local step.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

open scoped Pointwise in
/-- Apply the fusion endpoint after discharging its Thompson and normalizer inputs. -/
theorem isPSp_of_source_thompson_data_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  apply isPSp_of_thompson_local_data_at h₀ h structural D m z H₀ C inferInstance
    (thompson_normalizer_le_generated_at h structural D m z H₀ hnormal supplement) _ hpair
  intro a ha hai
  obtain ⟨c, hc, hac⟩ := hr a ha hai
  exact ⟨c, hc, (thompson_eq_plane_core D z H₀ C hnormal).symm ▸ hac⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
