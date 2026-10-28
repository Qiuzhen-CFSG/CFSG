module
public import Theory.SpecificGroups.Alternating.FiveSquareSylowObstruction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPairHeld
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart
public import Theory.SpecificGroups.Rudvalis.Model.Order

/-!
# The alternating-five square in the remaining invariant containers

A full Sylow preserving an A₅ square has an involution in its action
kernel, since the square has automorphism group of order 28800. Held's
involution centralizers have order indivisible by 25; Rudvalis's have
order indivisible by nine. Both contradict a centralized square of order
3600. The involution is constructed in the literal carrier, with no lift
across a two-kernel. These are the two remaining sporadic inputs for the
invariant common-component subcase of Aschbacher–Smith 5.2.2, p.648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.LargerInvariant
open Theory.SpecificGroups.Alternating

/-- No full Held Sylow preserves an embedded A₅ square. -/
theorem held_no_square (S : Sylow 2 Held.He) (W : Subgroup Held.He)
    (hSW : (S : Subgroup Held.He) ≤ normalizer (W : Set Held.He))
    (e : W ≃* FiveSquareAutomorphisms.Pair) : False := by
  obtain ⟨z,hz,hd⟩ := FiveSquareFitting.exists_involution_centralizer_square
    ((pow_dvd_pow 2 (by decide : 8 ≤ 10)).trans Held.two_pow_ten_dvd_card) S W hSW e
  have hd25 : 25 ∣ Nat.card (centralizer ({z} : Set Held.He)) :=
    (by decide : 25 ∣ 3600).trans hd
  rw [←MulAut.fixedSubgroup_conj] at hd25
  rcases Held.InvolutionFixedData.Coverage.innerInvolutionCoverage z hz with ⟨c,rfl⟩ | ⟨c,rfl⟩
  · rw [←Nat.card_congr (Held.InvolutionFixedData.innerFixedEquiv (MulAut.conj c) Held.a).toEquiv] at hd25
    change 25 ∣ Nat.card Held.InvolutionFixedData.TwoA.centralizer at hd25
    rw [Held.InvolutionFixedData.TwoA.FiniteStructure.centralizer_card] at hd25
    norm_num at hd25
  · rw [←Nat.card_congr (Held.InvolutionFixedData.innerFixedEquiv (MulAut.conj c)
        (Held.TwoLocalCandidates.max5First^4)).toEquiv,
      Held.InvolutionFixedData.twoB_fixedSubgroup_card] at hd25
    norm_num at hd25

/-- No full Rudvalis Sylow preserves an embedded A₅ square. -/
theorem rudvalis_no_square (S : Sylow 2 Rudvalis.Model) (W : Subgroup Rudvalis.Model)
    (hSW : (S : Subgroup Rudvalis.Model) ≤ normalizer (W : Set Rudvalis.Model))
    (e : W ≃* FiveSquareAutomorphisms.Pair) : False := by
  obtain ⟨z,hz,hd⟩ := FiveSquareFitting.exists_involution_centralizer_square
    (by rw [Rudvalis.model_card]; norm_num) S W hSW e
  exact Rudvalis.InvolutionCentralizers.centralizer_not_nine z hz
    ((by decide : 9 ∣ 3600).trans hd)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.LargerInvariant
