module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Inputs
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import GorensteinWalter.A5
public import GorensteinWalter.LinearRingEquiv
public import GorensteinWalter.PSL2Cardinality
public import Theory.GroupTheory.SmallIndexSolvable

/-!
# The small-parameter sieve for the actual component quotient

A quasisimple quotient cannot be PSL₂(3): that group has order twelve
and is solvable. The field-five comparison with A₅, followed by its actual
field-four projective representation, makes PSL₂(5) a Bender model.
Thus the odd-prime row of the closure alternatives starts at seven. The
invariant linear and Held rows, including their original actor data, survive
unchanged; their generation remains a separate source obligation.

Source: Aschbacher--Smith 10.2.4 and 10.3.3, printed pp.747,756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender

private theorem not_quasisimple_psl_two_three {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] (hm : ClassicalGroup.IsPSL Q 2 3) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hc : Nat.card Q = 12 := by
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F
      ⟨3, 1, by decide, by decide, by decide, by simpa using hF⟩, hF]
    norm_num
  let P : Sylow 2 Q := Classical.choice inferInstance
  have hcop : Nat.Coprime (P : Subgroup Q).index (2 ^ 2) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr P.not_dvd_index).symm.pow_right 2
  have hi : (P : Subgroup Q).index ∣ 3 := hcop.dvd_of_dvd_mul_left
    (by simpa [hc] using (P : Subgroup Q).index_dvd_card)
  let : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  exact Group.IsPerfect.not_isSolvable Q ((P : Subgroup Q).isSolvable_of_index_le_four
    ((Nat.le_of_dvd (by decide : 0 < 3) hi).trans (by decide)))

private theorem bender_of_psl_two_five {Q : Type*} [Group Q]
    (hm : ClassicalGroup.IsPSL Q 2 5) : ClassificationModels.IsBenderModel Q := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let eA := (e.trans (GorensteinWalter.psl2RingEquiv eF).symm).trans
    GorensteinWalter.alternatingGroupFive_equiv_PSL2.some.symm
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  let e4 := (ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour).some
  exact .linear 2 (by decide)
    ⟨GaloisField 2 2, inferInstance, inferInstance, hfour, ⟨eA.trans e4.symm⟩⟩

/-- The no-Bender hypothesis removes the binary and prime-five alternatives
using actual model equivalences; quasisimplicity removes prime three. -/
theorem remainingModel_of_not_bender {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {I : Subgroup G}
    (hqs : IsQuasisimple (I ⧸ pCore 2 I))
    (hm : Overgroups.ClosureModel T I)
    (hn : ¬ ClassificationModels.IsBenderModel (I ⧸ pCore 2 I)) :
    RemainingModel T I := by
  rcases hm with hb | hp | hl | hh
  · obtain ⟨n, hn2, _, hmodel⟩ := hb
    exact (hn (.linear n hn2 hmodel)).elim
  · obtain ⟨p, hp, ho, hmodel⟩ := hp
    let := hqs
    have hp3 : p ≠ 3 := fun he => not_quasisimple_psl_two_three (he ▸ hmodel)
    have hp5 : p ≠ 5 := fun he => hn (bender_of_psl_two_five (he ▸ hmodel))
    have hp7 : 7 ≤ p := by
      have hge := hp.two_le
      obtain ⟨k, hk⟩ := ho
      omega
    exact Or.inl ⟨p, hp, ho, hp7, hmodel⟩
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr hh)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
