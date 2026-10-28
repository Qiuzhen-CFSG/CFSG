module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Perfectness
public import Theory.GroupAction.AutomorphismFixedResidualTransport

/-!+# The two-residual of a smaller binary triality carrier

Perfectness rules out every nontrivial finite two-group quotient, so the
two-residual and commutator of the genuine smaller carrier both equal the
whole group. This includes exponent one. An actual isomorphism from an
automorphism fixed subgroup transports its literal two-residual to that
commutator; the displayed map retains the original fixed-group isomorphism.

This discharges the smaller-residual input of the field-descent assembly for
Aschbacher–Smith 16.1.4(4), printed p.1171 (`refs/quasithin.pdf`). The separate
normalization and fixed-group descent are not asserted here. Perfectness is
proved from the actual root groups in `StandardTwoRank.Perfectness`, following
GLS3 2.2.7(b) and §§2.3–2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.EvenField

/-- A perfect finite binary triality carrier has no proper two-group quotient. -/
theorem smaller_pResidual_eq_top (m : ℕ) (hm : 0 < m) :
    pResidual 2 (BinaryCarrier m hm) = ⊤ := by
  apply (pResidual_eq_top_iff 2 _).mpr
  intro N hN hq
  let := hN
  have hs : Subsingleton (BinaryCarrier m hm ⧸ N) := by
    by_contra! hnontrivial
    exact Group.IsPerfect.not_isNilpotent (BinaryCarrier m hm ⧸ N) hq.isNilpotent
  apply top_unique
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (hs.elim _ _)

/-- The smaller-field identity required by 16.1.4(4), retaining exponent one. -/
theorem smaller_pResidual_eq_commutator (m : ℕ) (hm : 0 < m) :
    pResidual 2 (BinaryCarrier m hm) = commutator (BinaryCarrier m hm) := by
  rw [smaller_pResidual_eq_top, TwoRank.Perfectness.binary_commutator_eq_top]

/-- Transport through the actual smaller-field model isomorphism. -/
def smallerResidualEquivDerived {G : Type*} [Group G]
    (m : ℕ) (hm : 0 < m) (e : G ≃* BinaryCarrier m hm) :
    pResidual 2 G ≃* commutator (BinaryCarrier m hm) :=
  ((pResidual 2 G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr
      ((Subgroup.map_pResidual 2 e).trans (smaller_pResidual_eq_commutator m hm)))

@[simp] theorem smallerResidualEquivDerived_apply {G : Type*} [Group G]
    (m : ℕ) (hm : 0 < m) (e : G ≃* BinaryCarrier m hm) (x : pResidual 2 G) :
    (smallerResidualEquivDerived m hm e x : BinaryCarrier m hm) = e (x : G) := rfl

/-- The field-fixed consumer uses precisely this fixed subgroup and its own residual. -/
def fixedResidualEquivSmallerDerived {G : Type*} [Group G] (a : MulAut G)
    (m : ℕ) (hm : 0 < m) (e : a.fixedSubgroup ≃* BinaryCarrier m hm) :
    pResidual 2 a.fixedSubgroup ≃* commutator (BinaryCarrier m hm) :=
  smallerResidualEquivDerived m hm e

@[simp] theorem fixedResidualEquivSmallerDerived_apply {G : Type*} [Group G]
    (a : MulAut G) (m : ℕ) (hm : 0 < m)
    (e : a.fixedSubgroup ≃* BinaryCarrier m hm) (x : pResidual 2 a.fixedSubgroup) :
    (fixedResidualEquivSmallerDerived a m hm e x : BinaryCarrier m hm) =
      e (x : a.fixedSubgroup) := rfl

end Triality.Standard.EvenField
