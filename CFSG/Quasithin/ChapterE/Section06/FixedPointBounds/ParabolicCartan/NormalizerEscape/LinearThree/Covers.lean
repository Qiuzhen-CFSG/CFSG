module

public import Theory.SpecificGroups.PSL3.ScalarLiftTwoCore
public import Theory.GroupTheory.CComponent.QuotientLifting
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.LinearCovered

/-!
# The actual scalar SL3 cover of a source component

The C-component quotient by its two-core identifies with the actual component
image in X/O2(X). Subnormality makes the latter's two-core trivial. Applying
the scalar lift theorem to the literal comparison with the marked PSL3
component gives a surjection from SL3 with the required commuting square.
This includes field order four and retains the original source quotient.

Source: Aschbacher--Smith E.2.2(2b) and 4.4.13(1), printed pp.215--216,623--624.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels MarkedModels.DiagramHall ChapterB
variable {X : Type*} [Group X] [Finite X]
variable {F : Type*} [Field F] [Finite F]
public theorem linear_source_scalar_lift {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : sourceImage (minimalParabolicMax S hP) K ≃* PSL(3,F)) :
    ∃ k : SL(3,F) →* actorImage K, Function.Surjective k ∧
      (e.toMonoidHom.comp (linearSourceComparison S hP K)).comp k = Matrix.PSL3.projection F := by
  let := hqK
  let : IsQuasisimple (actorImage K) :=
    IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hsub : (actorImage K).IsSubnormal :=
    hK.subnormal.map (QuotientGroup.mk'_surjective (pCore 2 X))
  have hcore : pCore 2 (actorImage K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hsub,pCore_quotient_pCore_eq_bot]
    exact (actorImage K).subtype.ker_eq_bot (actorImage K).subtype_injective
  have h2 : Nat.card F ≠ 2 := by
    rw [hF]
    have hh : 2^1 < 2^n := Nat.pow_lt_pow_right (by decide) hn
    omega
  exact Matrix.PSL3.exists_scalar_lift_of_twoCore_eq_bot h2 _
    (e.surjective.comp (linearSourceComparison_surjective S hP K)) hcore
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
