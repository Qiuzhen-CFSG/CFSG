module

public import Theory.GroupAction.ThompsonAB

/-!
# A.1.18: Thompson's A × B lemma

Here A and B are commuting subgroups of a finite group represented on a
finite p-group G. Part (1) retains the source hypothesis A = O^p(A), rather
than imposing coprime order on A. Part (2) supplies the faithful action on
the actual B-fixed subgroup, with its induced A-action.

The reusable proof applies the P × Q lemma to prime-to-p generators.
For (2), the residual of the restriction kernel is killed by (1); normality
then puts that kernel in O_p(A). The source residual hypothesis on A is
retained in (2), although the kernel argument proves a stronger result.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, Lemma A.1.18, printed p.24.
-/

namespace CFSG.Quasithin.ChapterA

/-- A.1.18(1): centralizing C_G(B) forces A to centralize G. -/
public theorem lemma_A_1_18_1
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    [MulDistribMulAction H G] {p : ℕ} [Fact p.Prime]
    (A B : Subgroup H) (hG : IsPGroup p G) (hB : IsPGroup p B)
    (hA : pResidual p A = ⊤) (hAB : ⁅A, B⁆ = ⊥)
    (hfix : A ≤ fixingSubgroup H (FixedPoints.subgroup B G : Set G)) :
    A ≤ fixingSubgroup H (Set.univ : Set G) :=
  thompson_a_times_b_fixedPoints A B hG hB hA hAB hfix

/-- A.1.18(2): a faithful A-action with O_p(A) = 1 restricts faithfully
 to C_G(B). The displayed local instance is the literal restricted action. -/
public theorem lemma_A_1_18_2
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    [MulDistribMulAction H G] {p : ℕ} [Fact p.Prime]
    (A B : Subgroup H) [FaithfulSMul A G]
    (hG : IsPGroup p G) (hB : IsPGroup p B)
    (_hA : pResidual p A = ⊤) (hAB : ⁅A, B⁆ = ⊥)
    (hcore : pCore p A = ⊥) :
    let : IsInvariant A G (FixedPoints.subgroup B G) :=
      fixedPoints_isInvariant_of_normalizing_actor A B
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB).trans
          (Subgroup.centralizer_le_normalizer _))
    FaithfulSMul A (FixedPoints.subgroup B G) :=
  thompson_faithfulSMul_fixedPoints A B hG hB hAB hcore

end CFSG.Quasithin.ChapterA
