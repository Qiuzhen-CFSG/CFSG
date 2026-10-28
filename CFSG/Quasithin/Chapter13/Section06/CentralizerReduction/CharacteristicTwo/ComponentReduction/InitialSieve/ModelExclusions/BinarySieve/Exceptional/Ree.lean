module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.Exceptional.Transport
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups
public import Theory.GroupAction.AutomorphismOddOuter

/-!
# The Ree branch of the initial binary sieve

Use the actual fixed-group witness in IsReeF4At. Its outer automorphism
group has odd order dividing 2*n+1, with simplicity and perfectness inherited
from the component's central quotient. Thus every member of the marked
four-group acts innerly on that quotient, and faithfulness puts E* in K*.
The defining binary exponent remains 2*n+1.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927; the intrinsic
automorphism theorem uses GLS3 §2.5 and Remark A.2.4, printed p.33.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
open A5Module Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- The complete Ree field branch, for the literal fixed-group model witness. -/
theorem largeField_of_ree (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {n : ℕ} (hn : 1 ≤ n)
    (hi : IsReeF4At (NormalizerAction.componentImage K) n) :
    LargeField K a := by
  obtain ⟨d, ⟨e⟩⟩ := hi
  obtain ⟨hs, hp⟩ := exceptional_model_hypotheses K hK e
  let : IsSimpleGroup d.fixedGroup := hs
  let : Group.IsPerfect d.fixedGroup := hp
  have hodd : Odd (MulAut.conj : d.fixedGroup →* MulAut d.fixedGroup).range.index := by
    change Odd (Nat.card (MulAut.Outer d.fixedGroup))
    apply Nat.not_even_iff_odd.mp
    intro he
    have hd := (even_iff_two_dvd.mp he).trans (ReeF4.LocalBlockInput.outer_card_dvd hn d)
    omega
  refine ⟨2 * n + 1, by omega, .ree n hn ⟨d, ⟨e⟩⟩,
    EStar_le_component_of_model_involutive_fixers K hK a e ?_⟩
  intro S α hsq _
  obtain ⟨x, hx⟩ := MulAut.inner_of_sq_eq_one_of_odd_index hodd α hsq
  exact ⟨x, hx.symm⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
