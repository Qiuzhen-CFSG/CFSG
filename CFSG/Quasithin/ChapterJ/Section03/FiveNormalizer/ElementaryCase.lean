module
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.FixedGroups
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.Arithmetic
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.Local
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.SourceCompletion.Noncentral
public import Theory.GroupTheory.FullAutomizerNormalizerControl
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Five
/-!
# The source five-normalizer and elementary-branch exclusion

The original local hypotheses give N_G(B₅) order4000: its centralizer has
order1000, and the full automizer is realized inside H. In the elementary
branch, the literal normalizer of P has that same order once its two-part
is32. It therefore normalizes B₅, contradicting the proved source fusion.
The separate central-involution promotion discharges that two-part premise.

The five-core, quaternion and inverter witnesses are all constructed here
through their genuine earlier source theorems. Only J.3.1's ambient order and
the named promotion remain inputs.
Source: Aschbacher--Smith J.3.6, printed p.439.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

theorem five_normalizer_card (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    : Nat.card (normalizer (B5Image B5 : Set G))=4000 := by
  have hP := SourceCompletion.five_oddPart_card c B5
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  have hsurj : Function.Surjective (B5Image B5).normalizerMonoidHom := by
    intro a
    obtain ⟨n,hn⟩ := local_five_full_ambient_action B5 a
    exact ⟨n.val,hn⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ha := (prime_full_automizer (B5Image B5) (B5Image_card d.card_Z B5) hsurj).2
  have hc := c.G5_card B5 d.card_Z q
  rw [hP] at hc
  have hk : Nat.card (B5Image B5).normalizerMonoidHom.ker=1000 := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (B5Image B5 : Set G))).toEquiv]
    exact hc
  have he := (B5Image B5).normalizerMonoidHom.ker.card_mul_index
  rw [index_ker,hk,ha] at he
  exact he.symm

theorem five_oddPart_extraspecial_of_two_part (c : Choices d)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29)
    (h64 : ¬64∣Nat.card (normalizer (fiveOddPart B5 : Set G))) :
    IsExtraspecial 5 (fiveOddPart B5) := by
  have hP := SourceCompletion.five_oddPart_card c B5
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  obtain ⟨v⟩ := c.fiveInverterData_source B5
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply IsExtraspecial.of_noncommutative_card_prime_cube hP
  intro hcomm
  let := hcomm
  let := FiveInverterData.elementary_of_commutative c B5 q v hP
  have hNB := five_normalizer_card c B5
  have h32 : 32∣Nat.card (normalizer (fiveOddPart B5 : Set G)) := by
    have hd := card_dvd_of_le (normalizer_B5Image_le_normalizer_fiveOddPart B5)
    rw [hNB] at hd
    exact (by decide : 32∣4000).trans hd
  have hNP := five_normalizer_order_of_elementary_selfcentralizer hG (fiveOddPart B5)
    hP (fiveOddPart_self_centralizing_of_commutative c B5 q hP) h32 h64
  have hn : normalizer (fiveOddPart B5 : Set G) ≤ normalizer (B5Image B5 : Set G) :=
    (eq_of_le_of_card_ge (normalizer_B5Image_le_normalizer_fiveOddPart B5)
      (by rw [hNB,hNP])).symm.le
  exact FiveInverterData.noncommutative_of_normalizer_control c B5 q v hG hP hn hcomm

end CFSG.Quasithin.ChapterJ.Section03
