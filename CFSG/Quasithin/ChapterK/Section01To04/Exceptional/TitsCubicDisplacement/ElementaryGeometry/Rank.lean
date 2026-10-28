module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.Rank.Certificate
public import Theory.SpecificGroups.Tits.Atlas1600SylowTwo
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankSylow

/-!
# The unconditional Tits two-rank bound five

A kernel-checked 32-coloring separates distinct commuting square-one elements
in the certified 2048-element ATLAS Sylow subgroup. Restriction of this
coloring embeds every elementary abelian subgroup into `Fin 32`. The elementary
cardinality characterization of prime rank, Sylow conjugacy and the certified
Parrott–ATLAS equivalence then give the bound on the literal Parrott group.

Source: GM04 Table 13, internal p.53, used by Lemma 8.8, p.57;
Aschbacher–Smith K.3, printed p.457. `Rank/Source.md` describes the certificate.
`Rank.Application` discharges the rank premise of the actual local geometry
and representation consumers without changing the parent assembly.
-/

public section

open Tits Theory.GroupTheory
open Tits.ConverseLocalCoverage.DoubleCosetCertificate
open Tits.OuterOddSubgroups.OverlapCentralizers
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
open RankCertificate

private theorem fastNormalForm_eq (n : Fin 2048) :
    fastNormalForm n = (atlas1600SylowTwoNormalForm n).val := by
  simp [fastNormalForm, Packed.perm_eq, Packed.generator, atlas1600SylowTwoNormalForm_val]

private theorem val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
private theorem val_one : (1 : Atlas1600Group).val = 1 := rfl

private theorem squareTest_of_square (n : Fin 2048)
    (h : atlas1600SylowTwoNormalForm n ^ 2 = 1) : squareTest n = true := by
  have hp := congrArg (fun g : Atlas1600Group => g.val 0) h
  simpa only [squareTest, fastNormalForm_eq, beq_iff_eq, pow_two, val_mul, val_one,
    Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using hp

private theorem normalForm_color_injective (n m : Fin 2048)
    (hn : atlas1600SylowTwoNormalForm n ^ 2 = 1)
    (hm : atlas1600SylowTwoNormalForm m ^ 2 = 1)
    (hc : atlas1600SylowTwoNormalForm n * atlas1600SylowTwoNormalForm m =
      atlas1600SylowTwoNormalForm m * atlas1600SylowTwoNormalForm n)
    (hcolor : color (locate n) = color (locate m)) : n = m := by
  have hcn := candidate_locate n (squareTest_of_square n hn)
  have hcm := candidate_locate m (squareTest_of_square m hm)
  have ht : commuteTest (locate n) (locate m) = true := by
    have hp := congrArg (fun g : Atlas1600Group => g.val 0) hc
    simpa only [commuteTest, hcn, hcm, fastNormalForm_eq, beq_iff_eq,
      val_mul, Equiv.Perm.mul_apply] using hp
  have hi := color_separates (locate n) (locate m) hcolor ht
  simpa only [hcn, hcm] using congrArg candidate hi

/-- Every elementary abelian subgroup of the certified Sylow has order at most 32. -/
theorem sylow_elementary_card_le_thirty_two
    (E : Subgroup atlas1600SylowTwoSubgroup) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ 32 := by
  let := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  let idx (x : E) : Fin 2048 := atlas1600SylowTwoEquiv.symm x.val
  have hnf (x : E) : atlas1600SylowTwoNormalForm (idx x) = x.val.val := by
    simpa only [atlas1600SylowTwoEquiv_apply] using
      congrArg Subtype.val (atlas1600SylowTwoEquiv.apply_symm_apply x.val)
  let c (x : E) : Fin 32 := color (locate (idx x))
  have hinj : Function.Injective c := by
    intro x y hxy
    apply Subtype.ext
    apply atlas1600SylowTwoEquiv.symm.injective
    apply normalForm_color_injective (idx x) (idx y)
    · rw [hnf]
      exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian x.val x.property)
    · rw [hnf]
      exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian y.val y.property)
    · rw [hnf, hnf]
      exact congrArg (fun z : E => z.val.val) (mul_comm x y)
    · exact hxy
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective c hinj

/-- The concrete ATLAS model has two-rank at most five. -/
theorem atlas_two_rank_le_five : primeRank 2 Atlas1600Group ≤ 5 := by
  rw [atlas1600SylowTwo.primeRank_eq]
  rw [atlas1600SylowTwo_coe]
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  exact sylow_elementary_card_le_thirty_two E hE

/-- The certified Parrott–ATLAS equivalence gives the literal source rank bound. -/
theorem parrott_two_rank_le_five : primeRank 2 ParrottGroup ≤ 5 := by
  rw [primeRank_equiv 2 parrottFiniteImageEquiv]
  exact atlas_two_rank_le_five

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
