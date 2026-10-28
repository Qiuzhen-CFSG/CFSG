module

public import Stellmacher.SectionOne.NineCoreSupportPair
public import Stellmacher.SectionOne.NineCoreOrderThirtySixExclusion
public import Stellmacher.SectionOne.NineCoreWreathOffender
public import Stellmacher.SectionOne.NineCoreGenerationFromOffender

namespace Stellmacher.SectionOne
universe u

public theorem nineCore_oneJ_ne_bot
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (R : Sylow 2 K)
    (hgen : oddCore K ⊔ (R : Subgroup K) = ⊤)
    (hunique : IsUniqueMaximalContaining (R : Subgroup K) ⊤)
    (hVcard : Nat.card V = 16) (hoddcard : Nat.card (oddCore K) = 9)
    (X : Subgroup K) (hX : IsElementaryAbelian 2 X) (hXcard : Nat.card X = 4) :
    oneJ (V := V) (R : Subgroup K) ≠ ⊥ := by
  have hWnormal : (oddCore K).Normal := pPrimeCore_normal
  have hWelementary := nineCore_elementary_of_elementary_four h hoddcard X hX hXcard
  obtain ⟨hdivides, first, second, hcompl, hfirst, hsecond, hperm⟩ :=
    nineCore_support_pair_and_card_dvd (oddCore K) hWnormal hWelementary
      hoddcard hVcard h.action_faithful
  have hKcard := nineCore_card_seventy_two_of_dvd hoddcard X hXcard hdivides
    (nineCore_card_ne_thirty_six h R hgen hunique hoddcard X hX hXcard)
  exact oneJ_ne_bot_of_complementary_four_card_seventy_two R first second
    hcompl hfirst hsecond h.action_faithful hKcard hperm

#print axioms nineCore_oneJ_ne_bot
end Stellmacher.SectionOne
