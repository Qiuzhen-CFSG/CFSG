module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.SourceTransfers
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.G2
public import CFSG.Quasithin.ChapterC.Section03.A5.PSLThreeEven
public import CFSG.Quasithin.ChapterC.Section03.A5.SymplecticFour
public import CFSG.Quasithin.ChapterC.Section03.A5.ReeTits
public import CFSG.Quasithin.ChapterC.Section03.A5.TrialityEscape
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.Cardinality
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Triality.Model.QTKE
/-! The characteristic-two rank-two catalogue supplies an escaping characteristic-two overgroup invariant under every automorphism preserving the actual deleted-five layer. Linear, symplectic, Ree, Tits and small derived rows contain no such block; G2 and triality supply canonical invariant parabolics.
Source: Aschbacher–Smith 2.4.25, printed p.543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
open ChapterC Chapter1.Section02.LocalModels
variable {D : Type*} [Group D] [Finite D]
/-- The exact rank-two catalogue yields an invariant escape for the original deleted block. -/
theorem rank_two_invariant_obstruction [IsSimpleGroup D] [Group.IsPerfect D]
    (hm : RankTwoTheoremC D) (A : Subgroup D) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) :
    ∃ N : Subgroup D, N ∈ Chapter1.He D ∧ A ≤ N ∧
      (∀ a : MulAut D, ((blockU A).map A.subtype).map a.toMonoidHom =
        (blockU A).map A.subtype → N.map a.toMonoidHom = N) ∧
      ∀ Q : Sylow 2 N, A.subgroupOf N ∉ ChapterA.Section03.localCComponents Q := by
  cases hm with
  | linear f hf hm => exact (no_alternatingFive_of_pslThree_even A hA hf hm).elim
  | symplectic f hf hm => exact (no_alternatingFive_of_isPSp (by omega) hm A hA).elim
  | g2 f hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hq : 2 < Nat.card F := by
      rw [hF]
      calc
        2 = 2 ^ 1 := by norm_num
        _ < 2 ^ f := Nat.pow_lt_pow_right (by decide) (by omega)
    let B := A.map e.toMonoidHom
    have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv
      (e.subgroupMap A) hA
    obtain ⟨N,hN,hBN,hInv,hbad⟩ := G2.invariant_parabolic_obstruction hq B hB
    exact invariant_obstruction_of_equiv e A N hN hBN hInv hbad
  | triality f hf hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff D f (by omega)).mp hm
    let : IsSimpleGroup (Triality.Standard.BinaryCarrier f (by omega)) := e.symm.isSimpleGroup
    let : Group.IsPerfect (Triality.Standard.BinaryCarrier f (by omega)) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let B := A.map e.toMonoidHom
    have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv
      (e.subgroupMap A) hA
    obtain ⟨N,hN,hBN,hInv,hbad⟩ := native_triality_invariant_escape f hf B hB
    exact invariant_obstruction_of_equiv e A N hN hBN hInv hbad
  | ree m hm hmodel =>
    obtain ⟨d,⟨e⟩⟩ := hmodel
    exact (no_alternatingFive_of_reeF4_equiv hm (e.trans d.modelEquiv) A hA hc).elim
  | symplectic_derived hm =>
    obtain ⟨e⟩ := hm
    have hd := Chapter13.Section05.NormalBranch.DeletedFive.card_dvd_of_alternatingFive A hA hc
    have he := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
    rw [Nat.card_congr he.toEquiv,nat_card_alternatingGroup] at hd
    norm_num at hd
  | g2_derived hm =>
    obtain ⟨e⟩ := hm
    have hd := Chapter13.Section05.NormalBranch.DeletedFive.card_dvd_of_alternatingFive A hA hc
    rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  | tits hm =>
    obtain ⟨e⟩ := hm
    exact (no_alternatingFive_of_tits_equiv e A hA hc).elim
end CFSG.Quasithin.Chapter2.AlternatingTerminal
