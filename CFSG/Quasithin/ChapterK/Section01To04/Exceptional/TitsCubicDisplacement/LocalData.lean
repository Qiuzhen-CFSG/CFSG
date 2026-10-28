module

public import Theory.SpecificGroups.Tits.FiveFrobenius
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Finite local inputs for the Tits displacement calculation

These contracts concern the actual Parrott group, its involution centralizers
and its certified five-local subgroup. They contain no representation classification
or displacement conclusion. Their construction is a separate finite-group
calculation; this module does not assert that the contracts are inhabited.

The distinguished involution is the square of the quaternion generator in
the certified 5²:24 subgroup. On the nontrivial five-weights it pairs inverse
characters. The other local input makes every involution have a nontrivial
five-element commutator. Together these support a direct weight-space proof
of the inequalities in GM04 Lemma 8.8, without a small-degree catalogue.

Source: Guralnick--Malle, Classification of 2F-modules II, internal pp.6,
53 and 57 (Lemma 2.3, Table 13 and Lemma 8.8); DOI 10.1515/9783110198126.117.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
open Subgroup

/-- The literal five-complement involution, transported to Parrott's group. -/
@[expose] noncomputable def fiveInverter : Tits.ParrottGroup :=
  Tits.parrottFiniteImageEquiv.symm (Tits.FiveFrobenius.r ^ 2)

/-- Finite group calculations still needed for the source Tits argument.
The last clause concerns normality in the involution centralizer, not in Tits. -/
structure LocalGeometry : Prop where
  elementary_rank : primeRank 2 Tits.ParrottGroup ≤ 5
  five_commutator : ∀ t : Tits.ParrottGroup, t ≠ 1 → t ^ 2 = 1 →
    ∃ x k : Tits.ParrottGroup, k ∈ Tits.fiveKernel ∧ k ≠ 1 ∧
      IsConj k (t * x * t⁻¹ * x⁻¹)
  normal_elementary : ∀ t : Tits.ParrottGroup, t ≠ 1 → t ^ 2 = 1 →
    ∀ K : Subgroup Tits.ParrottGroup, K ≤ centralizer {t} →
      IsElementaryAbelian 2 K → (K.subgroupOf (centralizer {t})).Normal →
      (∀ k ∈ K, ¬ IsConj fiveInverter k) → Nat.card K ≤ 16

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
