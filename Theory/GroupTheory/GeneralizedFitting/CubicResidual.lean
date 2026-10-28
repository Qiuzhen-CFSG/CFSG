module
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PCoreFrattiniQuotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The generalized Fitting subgroup of a core-free cubic residual extension

If the two-core is trivial and the two-residual has order three, the
three-core is exactly that residual. Its two-group quotient makes it
self-centralizing, so it is the whole generalized Fitting subgroup.
This identifies the actual actor in Aschbacher--Smith C.1.17 for the selected
binary Baumann factor of C.1.26, printed pp.126 and132.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {A : Type*} [Group A] [Finite A]

/-- The actor is the literal original two-residual. -/
theorem generalizedFitting_eq_residual_of_cubic
    (hcore : pCore 2 A = ⊥) (hR : Nat.card (pResidual 2 A) = 3) :
    generalizedFitting A = pResidual 2 A := by
  let R := pResidual 2 A
  have hpR : IsPGroup 3 R := IsPGroup.of_card (n := 1) (by simpa using hR)
  have hRcore : R ≤ pCore 3 A := le_sSup ⟨inferInstance,hpR⟩
  have hQ : IsPGroup 2 (A ⧸ R) := isPGroup_quotient_pResidual 2
  have hcoreR : pCore 3 A ≤ R := by
    let q := QuotientGroup.mk' R
    have hd := IsPGroup.disjoint_of_ne 3 2 (by decide)
      ((pCore 3 A).map q) ((pCore 3 A).map q)
      (pCore_isPGroup.map q) (hQ.to_subgroup _)
    have hb : (pCore 3 A).map q = ⊥ := by simpa using hd.eq_bot
    exact ((Subgroup.map_eq_bot_iff _).mp hb).trans_eq (QuotientGroup.ker_mk' R)
  have he : pCore 3 A = R := le_antisymm hcoreR hRcore
  have hQ' : IsPGroup 2 (A ⧸ pCore 3 A) :=
    hQ.of_equiv (QuotientGroup.quotientMulEquivOfEq he.symm)
  exact (generalizedFitting_eq_pCore_of_selfCentralizing 3
    (centralizer_pCore_le_of_quotient_isPGroup 3 2 hcore hQ')).trans he
end Theory.GroupTheory
