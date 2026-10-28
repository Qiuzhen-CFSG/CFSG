module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.LinearSource
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import GorensteinWalter.A5
public import GorensteinWalter.LinearRingEquiv
public import Theory.GroupTheory.SmallIndexSolvable

/-!
# Small prime parameters in the paired PSL₂ branch

The field-three group has order twelve and is solvable, so it cannot be a
component. The actual field-five comparison with A₅ and the field-four
projective action transport that case to the completed binary SL₂ branch.
The latter retains its linear alternative as well as its dihedral one.

Source: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
noncomputable section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
variable {H : Type*} [Group H] [Finite H]

theorem component_not_equiv_field_three
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 3)
    {K : Subgroup H} (hK : IsComponent H K) (e : K ≃* PSL(2,F)) : False := by
  let := hK.2
  have hc : Nat.card K = 12 := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨3,1,by decide,by decide,by decide,by simpa using hF⟩,hF]
    norm_num
  let P : Sylow 2 K := Classical.choice inferInstance
  have hcop : Nat.Coprime (P : Subgroup K).index (2 ^ 2) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr P.not_dvd_index).symm.pow_right 2
  have hi : (P : Subgroup K).index ∣ 3 := hcop.dvd_of_dvd_mul_left
    (by simpa [hc] using (P : Subgroup K).index_dvd_card)
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  exact Group.IsPerfect.not_isSolvable K ((P : Subgroup K).isSolvable_of_index_le_four
    ((Nat.le_of_dvd (by decide : 0 < 3) hi).trans (by decide)))

theorem source_five_pair
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 5)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬K.Normal)
    (e : K ≃* PSL(2,F)) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hV : V ≠ ⊥) : PairedBender.LinearAlternative T (ChapterB.minimalParabolicMax T hP) V 2 := by
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let eA : K ≃* alternatingGroup (Fin 5) := (e.trans (GorensteinWalter.psl2RingEquiv eF).symm).trans
    GorensteinWalter.alternatingGroupFive_equiv_PSL2.some.symm
  have hfour : Nat.card (GaloisField 2 2) = 4 := by rw [GaloisField.card 2 2 (by decide)]; norm_num
  let e4 := (ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour).some
  let eL : K ≃* SL(2,GaloisField 2 2) := (eA.trans e4.symm).trans
    (SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (GaloisField 2 2)).symm
  exact PairedBender.source_linear_pair (by decide : 1 < 2) hfour hH T hP hs hJ hK hC
    hgen hnot eL V hVT hVM hV

end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
