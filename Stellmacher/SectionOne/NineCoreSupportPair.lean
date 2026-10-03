module

public import Stellmacher.SectionOne.NineCoreSupportBound
public import Stellmacher.SectionOne.NineCoreSupportDecomposition

@[expose] public section
namespace Stellmacher.SectionOne

universe u

theorem nineCore_support_pair_and_card_dvd
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (W : Subgroup K) (hWnormal : W.Normal)
    (hWelementary : IsElementaryAbelian 3 W)
    (hWcard : Nat.card W = 9) (hVcard : Nat.card V = 16)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥) :
    Nat.card K ∣ 72 ∧
      ∃ first second : Subgroup V,
        IsCompl first second ∧ Nat.card first = 4 ∧ Nat.card second = 4 ∧
        ∀ element : K,
          (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first ∧
           second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second) ∨
          (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second ∧
           second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first) := by
  obtain ⟨first, second, hcompl, hfirst, hsecond, hperm⟩ :=
    nineCore_support_decomposition W hWnormal hWelementary hWcard hVcard hfaith
  refine ⟨nineCoreSupport_card_dvd_of_complementary_four first second hcompl
    hfirst hsecond hfaith hperm, ?_⟩
  exact ⟨first, second, hcompl, hfirst, hsecond, hperm⟩

end Stellmacher.SectionOne
