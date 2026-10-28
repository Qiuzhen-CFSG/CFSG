module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.GroupTheory.GeneralizedFitting.NilpotentComponentPreimage
public import Theory.Quasithin.Rank
/-!
# The nilpotent-radical consequence of A.3.6

The exact universal A.3.6 implication is retained as an earlier-source input.
Its common clauses say that the Fitting subgroup has index two in the
solvable radical, or equals the center. A nilpotent radical is contained in
the Fitting subgroup, excluding the first case. In the second, the perfect
group centrally covers its quasisimple Fitting quotient, so is quasisimple.

We apply this to the actual two-core quotient of an SQTK C-component.
Quotient SQTK follows only for this two-group kernel, by odd-prime rank
monotonicity. No arbitrary quotient closure, homocyclic exponent bound,
center–Frattini equality, or later chapter input is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6,
pp.43–45; application to B.5.2, pp.103–104. The universal premise remains
with source producer `qt-a03-sqtk-structure`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u

/-- The exact earlier A.3.6 implication, with no center–Frattini or exponent
condition. Its source producer is `qt-a03-sqtk-structure`. -/
def A36Input (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], IsSQTK K X → pCore 2 X = ⊥ →
    ∀ C : Subgroup X, C.IsCComponent → A36Conclusion C

variable {D : Type u} [Group D] [Finite D]

omit [Finite D] in
/-- The common A.3.6 clauses force quasisimplicity if the radical is nilpotent. -/
theorem A36Common.isQuasisimple_of_nilpotent_radical
    [Group.IsPerfect D] [Group.IsNilpotent (solvableRadical D)]
    (h : A36Common D) : IsQuasisimple D := by
  have hle : solvableRadical D ≤ fittingSubgroup D :=
    le_sSup ⟨inferInstance, inferInstance⟩
  have hcentral : fittingSubgroup D ≤ center D := by
    rcases h.2.2.1 with hi | hz
    · have hone := relIndex_eq_one.mpr hle
      rw [hi.2.2] at hone
      omega
    · exact hz.1.le
  let : IsQuasisimple (D ⧸ fittingSubgroup D) := h.2.1
  exact (show PerfectCentralCovering.Cover D (D ⧸ fittingSubgroup D) from
    { toMonoidHom := QuotientGroup.mk' _
      surjective := QuotientGroup.mk'_surjective _
      isPerfect := inferInstance
      ker_le_center := by rwa [QuotientGroup.ker_mk'] }).isQuasisimple

/-- A.3.6 excludes the index-two radical branch when the radical is nilpotent. -/
theorem quasisimple_of_a36_of_nilpotent_radical {K : GroupClass.{u}}
    (hA36 : A36Input K) (hsq : IsSQTK K D) (h2 : pCore 2 D = ⊥)
    (hc : (⊤ : Subgroup D).IsCComponent)
    [Group.IsNilpotent (solvableRadical D)] : IsQuasisimple D := by
  have h := (hA36 D hsq h2 ⊤ hc).2
  let : Group.IsPerfect (⊤ : Subgroup D) := hc.perfect
  let : Group.IsNilpotent (solvableRadical (⊤ : Subgroup D)) := by
    rw [← map_solvableRadical_equiv (topEquiv : (⊤ : Subgroup D) ≃* D).symm]
    exact Group.nilpotent_of_surjective _
      ((topEquiv : (⊤ : Subgroup D) ≃* D).symm.toMonoidHom.subgroupMap_surjective _)
  let : IsQuasisimple (⊤ : Subgroup D) := h.isQuasisimple_of_nilpotent_radical
  exact IsQuasisimple.of_mulEquiv topEquiv

/-- The source two-core quotient of an SQTK C-component is quasisimple
when its radical is nilpotent. This consumes only A.3.6. -/
theorem quasisimple_twoCore_quotient_of_a36 {H : Type u} [Group H] [Finite H]
    {K : GroupClass.{u}} (hA36 : A36Input K) (hsq : IsSQTK K H)
    {C : Subgroup H} (hC : C.IsCComponent)
    [Group.IsNilpotent (solvableRadical C)] :
    IsQuasisimple (C ⧸ pCore 2 C) := by
  let Q := pCore 2 C
  let D := C ⧸ Q
  let q := QuotientGroup.mk' Q
  let : Group.IsNilpotent Q := pCore_isNilpotent (p := 2)
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let : Group.IsNilpotent (solvableRadical D) :=
    radical_nilpotent_of_surjective q (QuotientGroup.mk'_surjective Q)
  have htop : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using hC.subgroupOf le_rfl
  have hdtop : (⊤ : Subgroup D).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)] using
      htop.map_quotient Q
  have hCsq := hsq.subgroup C
  have hDsq : IsSQTK K D := by
    refine ⟨?_, hCsq.isKGroup.quotient Q⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho Q pCore_isPGroup).trans
      (hCsq.stronglyQuasithin p hp ho)
  exact quasisimple_of_a36_of_nilpotent_radical hA36 hDsq
    (pCore_quotient_pCore_eq_bot 2) hdtop
end CFSG.Quasithin.Chapter1.Section02
