module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.Common
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechCentralizerSections
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LyonsThompsonSections
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.BabyMonsterSection
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.MonsterLocalObstruction
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.FischerCentralizerSections
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.ONanEmbedding
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22Centralizer
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinaryRank
public import Theory.Quasithin.CoprimeLocalRank

/-!
# Actual sporadic local sections under proper-section induction

Use the concrete involution-centralizer quotient maps and apply the original
proper-section induction hypothesis after lifting to the original group.
The O’Nan argument also forces the original center prime to be three, using
its actual local three-rank and coprime-kernel rank transfer.

Source: Aschbacher–Smith A.2.19, printed pp.40–41 (Case I and Case II).
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
universe u v
variable {G : Type u} [Group G] [Finite G]

private lemma false_of_simple_equiv_data [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G)
    {H T : Type*} [Group H] [Group T] [IsSimpleGroup T]
    (e : G ≃* H) (d : InvolutionCentralizerQuotientData H T)
    (hnT : ¬ IsMulCommutative T) (hr : 2 < primeRank 3 T) : False := by
  let : IsQuasisimple G := simple_quasisimple hna
  let : IsSimpleGroup H := e.symm.isSimpleGroup
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact false_of_centralizer_quotient ih hG hK e.toMonoidHom e.surjective
    (center_eq_bot_of_simple (Group.IsPerfect.not_isMulCommutative H)) d hnT hr

public theorem simple_co1 [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G)
    (e : G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) : False := by
  let : IsSimpleGroup (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) := leechPOmega8PlusTwo_simple
  with_reducible
    exact false_of_simple_equiv_data (H := _root_.Sporadic.LeechRelated.Co1.Carrier)
      (T := ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) ih hG hK hna e
      LeechSections.Co1.classicalQuotientData leechPOmega8PlusTwo_nonabelian leechPOmega8PlusTwo_primeRank_three_gt_two

public theorem cover_co1 [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) : False := by
  let : IsSimpleGroup (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) := leechPOmega8PlusTwo_simple
  with_reducible
    exact false_of_cover_centralizer_quotient (H := _root_.Sporadic.LeechRelated.Co1.Carrier)
      (T := ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) ih hG hK e
      LeechSections.Co1.classicalQuotientData leechPOmega8PlusTwo_nonabelian leechPOmega8PlusTwo_primeRank_three_gt_two

public theorem simple_co2 [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G)
    (e : G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) : False := by
  let := leechPSp6Two_simple
  exact false_of_simple_equiv_data ih hG hK hna e
    LeechSections.co2CentralizerQuotient leechPSp6Two_nonabelian leechPSp6Two_primeRank_three_gt_two

public theorem cover_co2 [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) : False := by
  let := leechPSp6Two_simple
  exact false_of_cover_centralizer_quotient ih hG hK e
    LeechSections.co2CentralizerQuotient leechPSp6Two_nonabelian leechPSp6Two_primeRank_three_gt_two

public theorem simple_co3 [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G)
    (e : G ≃* _root_.Sporadic.LeechRelated.Co3.Carrier) : False := by
  let := leechPSp6Two_simple
  exact false_of_simple_equiv_data ih hG hK hna e
    CFSG.Quasithin.ChapterA.Sporadic.LeechSections.co3QuotientData leechPSp6Two_nonabelian leechPSp6Two_primeRank_three_gt_two

public theorem cover_co3 [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.Co3.Carrier) : False := by
  let := leechPSp6Two_simple
  exact false_of_cover_centralizer_quotient ih hG hK e
    CFSG.Quasithin.ChapterA.Sporadic.LeechSections.co3QuotientData leechPSp6Two_nonabelian leechPSp6Two_primeRank_three_gt_two

public theorem simple_suz [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G)
    (e : G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier) : False := by
  let := leechPOmega6MinusTwo_simple
  exact false_of_simple_equiv_data ih hG hK hna e
    SuzCentralizerSection.quotientData leechPOmega6MinusTwo_nonabelian leechPOmega6MinusTwo_primeRank_three_gt_two

public theorem cover_suz [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier) : False := by
  let := leechPOmega6MinusTwo_simple
  exact false_of_cover_centralizer_quotient ih hG hK e
    SuzCentralizerSection.quotientData leechPOmega6MinusTwo_nonabelian leechPOmega6MinusTwo_primeRank_three_gt_two

public theorem simple_ly [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G)
    (e : G ≃* Lyons.LyonsGroup) : False := by
  let := lyonsA11_simple
  exact false_of_simple_equiv_data ih hG hK hna e
    lyonsA11Section lyonsA11_nonabelian lyonsA11_primeRank_three_gt_two

public theorem cover_ly [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* Lyons.LyonsGroup) : False := by
  let := lyonsA11_simple
  exact false_of_cover_centralizer_quotient ih hG hK e
    lyonsA11Section lyonsA11_nonabelian lyonsA11_primeRank_three_gt_two

public theorem simple_th [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G)
    (e : G ≃* Thompson.Model) : False := by
  let := thompsonA9_simple
  with_reducible
    exact false_of_simple_equiv_data (H := Thompson.Model) (T := alternatingGroup (Fin 9)) ih hG hK hna e
      thompsonA9Section thompsonA9_nonabelian thompsonA9_primeRank_three_gt_two

public theorem cover_th [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* Thompson.Model) : False := by
  let := thompsonA9_simple
  with_reducible
    exact false_of_cover_centralizer_quotient (H := Thompson.Model) (T := alternatingGroup (Fin 9)) ih hG hK e
      thompsonA9Section thompsonA9_nonabelian thompsonA9_primeRank_three_gt_two

public theorem simple_babyMonster [IsSimpleGroup G]
    (e : G ≃* BabyMonster.Carrier) (hG : IsQuasithin G) : False :=
  not_quasithin_of_babyMonster_equiv e hG

public theorem cover_babyMonster [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* BabyMonster.Carrier) : False := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : Nontrivial BabyMonster.Carrier := e.injective.nontrivial
  let := babyMonster_section_simple
  exact false_of_cover_centralizer_quotient ih hG hK e
    (babyMonster_alternatingNineQuotientData (MulEquiv.refl _))
    (by
      intro hcomm
      let := hcomm
      obtain ⟨a,b,hne⟩ := babyMonster_section_nonabelian
      exact hne (mul_comm' a b)) babyMonster_section_three_rank

public theorem simple_monster [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G) (e : G ≃* _root_.Sporadic.Monster.GriessGroup) : False := by
  have hz := center_eq_bot_of_simple hna
  let eQ : G ⧸ center G ≃* _root_.Sporadic.Monster.GriessGroup :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e
  apply MonsterLocalObstruction.false_of_center_eq_bot eQ hz
  intro M hM hl T _ _ _ hn hT
  exact proper_section_rank_bound ih hG hK hn hM hl hT 3 (by decide) (by decide)

public theorem cover_monster [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.Monster.GriessGroup)
    (ho : Odd (Nat.card (center G))) : False := by
  apply MonsterLocalObstruction.false_of_odd_center e ho
  intro M hM hl T _ _ _ hn hT
  exact proper_section_rank_bound ih hG hK hn hM hl hT 3 (by decide) (by decide)

public theorem fi22_not_quasithin : ¬ IsQuasithin _root_.Sporadic.Fischer.Fi22.Carrier := by
  obtain ⟨t,L,f,ht,hL,hf,hker⟩ := _root_.Sporadic.Fischer.Fi22.exists_unitary_section
  let d : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi22.Carrier
      Theory.SpecificGroups.U6Two.Carrier := ⟨t,ht,L,hL,f,hf⟩
  exact d.not_quasithin_of_rank hker 3 (by decide) Theory.SpecificGroups.U6Two.three_le_primeRank

public theorem simple_fi22 (e : G ≃* _root_.Sporadic.Fischer.Fi22.Carrier) (hG : IsQuasithin G) : False :=
  fi22_not_quasithin (isQuasithin_of_equiv e hG)

public theorem simple_onan (e : G ≃* ONan.Model) (hG : IsQuasithin G) : False :=
  onan_not_quasithin (isQuasithin_of_equiv e hG)

public theorem cover_onan_prime_three {p : ℕ} (hp : p.Prime)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* ONan.Model)
    (hG : IsQuasithin G) : p = 3 := by
  by_contra hne
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n,hn⟩ := hP.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card (projection e).ker) := by
    rw [projection_ker,hn]
    exact ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hne)).pow_right n
  have hr := twoLocalPrimeRank_le_of_surjective_of_coprime 3 (projection e)
    (projection_surjective e) hc
  have hb := isQuasithin_iff_twoLocalPrimeRank.mp hG 3 (by decide) (by decide)
  have hh := onan_three_le_twoLocalPrimeRank
  omega

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
