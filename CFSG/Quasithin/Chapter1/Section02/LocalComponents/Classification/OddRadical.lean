module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.NilpotentRadical

/-!
# Quasisimplicity when the two-core quotient has odd radical

The common clauses of A.3.6 make the Fitting subgroup either central or of
index two in the solvable radical. Odd order excludes the latter branch.
The perfect central cover of the resulting quasisimple quotient is therefore
quasisimple. This is the precise consequence used for the lifted component
in the Goldschmidt triple of 14.6.10(5).

Source: Aschbacher--Smith A.3.6 and 1.2.1(4), printed pp.43--45,504;
application in 14.6.10(5), printed p.1029.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {D : Type u} [Group D] [Finite D]

omit [Finite D] in
/-- The noncentral radical branch of A.3.6 has even order. -/
theorem A36Common.isQuasisimple_of_odd_radical
    [Group.IsPerfect D] (h : A36Common D)
    (ho : Odd (Nat.card (solvableRadical D))) : IsQuasisimple D := by
  have hcentral : fittingSubgroup D ≤ center D := by
    rcases h.2.2.1 with hi | hz
    · have hd := (fittingSubgroup D).relIndex_dvd_card (solvableRadical D)
      rw [hi.2.2] at hd
      exact (ho.not_two_dvd_nat hd).elim
    · exact hz.1.le
  let : IsQuasisimple (D ⧸ fittingSubgroup D) := h.2.1
  exact (show PerfectCentralCovering.Cover D (D ⧸ fittingSubgroup D) from
    { toMonoidHom := QuotientGroup.mk' _
      surjective := QuotientGroup.mk'_surjective _
      isPerfect := inferInstance
      ker_le_center := by rwa [QuotientGroup.ker_mk'] }).isQuasisimple

/-- Apply the genuine A.3.6 input to a C-component whose radical has odd order. -/
theorem quasisimple_of_a36_of_odd_radical {κ : GroupClass.{u}}
    (hA36 : A36Input κ) (hsq : IsSQTK κ D) (h2 : pCore 2 D = ⊥)
    (hc : (⊤ : Subgroup D).IsCComponent)
    (ho : Odd (Nat.card (solvableRadical D))) : IsQuasisimple D := by
  have h := (hA36 D hsq h2 ⊤ hc).2
  let : Group.IsPerfect (⊤ : Subgroup D) := hc.perfect
  have hodd : Odd (Nat.card (solvableRadical (⊤ : Subgroup D))) := by
    rw [← map_solvableRadical_equiv (topEquiv : (⊤ : Subgroup D) ≃* D).symm]
    exact (Nat.card_congr ((topEquiv : (⊤ : Subgroup D) ≃* D).symm.subgroupMap
      (solvableRadical D)).toEquiv) ▸ ho
  let : IsQuasisimple (⊤ : Subgroup D) := h.isQuasisimple_of_odd_radical hodd
  exact IsQuasisimple.of_mulEquiv topEquiv

/-- The actual two-core quotient of an SQTK C-component is quasisimple
when its solvable radical has odd order. -/
theorem quasisimple_twoCore_quotient_of_a36_of_odd_radical
    {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
    (hA36 : A36Input κ) (hsq : IsSQTK κ H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (ho : Odd (Nat.card (solvableRadical (C ⧸ pCore 2 C)))) :
    IsQuasisimple (C ⧸ pCore 2 C) := by
  let Q := pCore 2 C
  let D := C ⧸ Q
  let : Group.IsNilpotent Q := pCore_isNilpotent (p := 2)
  have htop : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using hC.subgroupOf le_rfl
  have hdtop : (⊤ : Subgroup D).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)] using
      htop.map_quotient Q
  have hCsq := hsq.subgroup C
  have hDsq : IsSQTK κ D := by
    refine ⟨?_,hCsq.isKGroup.quotient Q⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho Q pCore_isPGroup).trans
      (hCsq.stronglyQuasithin p hp ho)
  exact quasisimple_of_a36_of_odd_radical hA36 hDsq
    (pCore_quotient_pCore_eq_bot 2) hdtop ho

end CFSG.Quasithin.Chapter1.Section02
