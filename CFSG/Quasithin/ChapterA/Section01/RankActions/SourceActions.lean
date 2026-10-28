module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.AutomorphismQuotient
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ResidualActions
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Automorphisms

/-!
# Residual two-subgroup restrictions from the source hypotheses

The small-rank automorphism representation from A.1.25 and the generalized
Fitting action detector A.1.9 discharge both independent inputs of A.1.26.
The actual commutator-generated two-subgroup centralizes the odd core in
the elementary case; in the solvable strongly quasithin case, passing to
the two-core quotient puts that subgroup in the two-core.

The SQTK specialization retains the original source hypothesis, while its
strongly quasithin version records that the K-group assumption is unused.
The elementary strongly quasithin specialization supplies the rank bounds
for the odd-core application in 15.4.22.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.1.26, printed pp.25–26; Lemma 15.4.22, printed p.1165.
-/

public section

namespace CFSG.Quasithin.ChapterA

open Subgroup RankActions

universe u

variable {H : Type u} [Group H] [Finite H]

/-- A.1.26(1): the elementary commutator-generated two-subgroup centralizes
the entire odd core. All representation and Fitting detection inputs are
discharged by A.1.25(2) and A.1.9. -/
theorem lemma_A_1_26_1
    (X V : Subgroup H) (hX : pResidual 2 X = ⊤) (hV : IsPGroup 2 V)
    (hcomm : V = ⁅V, X⁆) (hphi : frattini V = ⊥)
    (hrank : ∀ (p : ℕ) [Fact p.Prime], Odd p → primeRank p (pCore p H) ≤ 2) :
    ⁅V, pPrimeCore 2 H⁆ = ⊥ :=
  oddCore_centralization_of_representation_and_fStarInput
    smallRankAutomorphismRepresentation pGroupFStarCentralizationInput
    X V hX hV hcomm hphi hrank

/-- The strongly quasithin elementary case of A.1.26(1). This is the
odd-core centralization used in the original quotient of 15.4.22. -/
theorem lemma_A_1_26_1_of_stronglyQuasithin
    (hsqt : IsStronglyQuasithin H) (X V : Subgroup H)
    (hX : IsPPerfect 2 X) [IsElementaryAbelian 2 V]
    (hcomm : ⁅V, X⁆ = V) : ⁅V, pPrimeCore 2 H⁆ = ⊥ := by
  have hV : IsPGroup 2 V := IsElementaryAbelian.isPGroup 2 V
  let : Fact (IsPGroup 2 V) := ⟨hV⟩
  exact lemma_A_1_26_1 X V ((pResidual_eq_top_iff 2 X).mpr hX) hV hcomm.symm
    (frattini_eq_bot_of_isElementaryAbelian (R := V) (p := 2))
    (fun p _ hp => (Theory.GroupTheory.primeRank_le_of_injective p
      (pCore p H).subtype Subtype.val_injective).trans (hsqt p Fact.out hp))

/-- A.1.26(2) needs only solvability and strong quasithinness. The
{2,3}-residual is the intersection of normal subgroups with {2,3}-group
quotient, and the subgroup need not be elementary abelian. -/
theorem lemma_A_1_26_2_of_stronglyQuasithin
    [Group.IsSolvable H] (hsqt : IsStronglyQuasithin H)
    (X V : Subgroup H) (hX : piResidual twoThreePrimes X = ⊤)
    (hV : IsPGroup 2 V) (hcomm : V = ⁅V, X⁆) : V ≤ pCore 2 H :=
  twoCore_containment_of_representation smallRankAutomorphismRepresentation
    hsqt X V hX hV hcomm

/-- A.1.26(2), with the source solvable SQTK hypothesis and every
independent action input discharged. -/
theorem lemma_A_1_26_2
    [Group.IsSolvable H] {K : GroupClass.{u}} (hsqtk : IsSQTK K H)
    (X V : Subgroup H) (hX : piResidual twoThreePrimes X = ⊤)
    (hV : IsPGroup 2 V) (hcomm : V = ⁅V, X⁆) : V ≤ pCore 2 H :=
  lemma_A_1_26_2_of_stronglyQuasithin hsqtk.stronglyQuasithin X V hX hV hcomm

end CFSG.Quasithin.ChapterA
