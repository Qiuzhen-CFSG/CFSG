module

public import Theory.Mathieu.M22.UniversalMultiplier.TwoRankSource

/-!
# The M₂₂ center obstruction in 12.7.5

The source component has two-group center and contains the actual elementary
four-group Vt in that center. Apply the cyclic-kernel theorem to the given
comparison after the literal central quotient map. Its cyclic center cannot
contain Vt. This preserves the original group, comparison and central subgroup.

Source: Aschbacher–Smith 12.7.5, printed p.840, combined manuscript of 1 March 2004.
The other component alternatives and earlier source deductions stay with the
section's assembly owner.
-/

public section

namespace CFSG.Quasithin.Chapter12.Section07.Preliminaries.M22CenterSource
open Subgroup PerfectCentralCovering Theory.GroupTheory Sporadic.Mathieu

/-- The literal M₂₂ central-quotient alternative in 12.7.5 has cyclic two-center. -/
theorem center_isCyclic {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (e : K ⧸ center K ≃* M22) (hp : IsPGroup 2 (center K)) :
    IsCyclic (center K) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hker : q.ker = center K :=
    (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (center K))
      e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' (center K))
  let f : Cover K M22 := {
    toMonoidHom := q
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective (center K))
    isPerfect := inferInstance
    ker_le_center := hker.le }
  have hf : IsPGroup 2 f.toMonoidHom.ker := by change IsPGroup 2 q.ker; rw [hker]; exact hp
  have hc := M22UniversalMultiplier.TwoRankSource.twoPrimary_kernel_isCyclic f hf
  change IsCyclic q.ker at hc
  rw [hker] at hc
  exact hc

/-- The actual elementary four-group `Vt ≤ Z(K)` excludes the M₂₂ alternative
in 12.7.5. The original quotient comparison and central subgroup are retained. -/
theorem exclude_m22_of_central_four {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (e : K ⧸ center K ≃* M22) (hp : IsPGroup 2 (center K))
    (Vt : Subgroup K) [IsElementaryAbelian 2 Vt]
    (hVt : Vt ≤ center K) (hcard : Nat.card Vt = 4) : False := by
  let : IsCyclic (center K) := center_isCyclic e hp
  let : IsCyclic Vt := isCyclic_of_injective (inclusion hVt) (inclusion_injective hVt)
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2)
    (by simpa using hcard) inferInstance

end CFSG.Quasithin.Chapter12.Section07.Preliminaries.M22CenterSource
