module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Fourth

/-!
# The surviving alternatives with the original component marking

All four surviving alternatives retain their complete local clauses.
Their module layers are additionally transported into the original group,
using one common identification of L/O₂(L). In particular the third case
keeps the dual action, and the fifth keeps the local point radical.

Source: Aschbacher–Smith, C.1.34(1)–(3),(5), printed pp.136–137,
and its use in 15.3.23, printed p.1128.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases

variable {G : Type*} [Group G] {L H : Subgroup G}

/-- Full local clauses together with the original ambient layers and one marking.
The radical and point-stabilizer clauses belong to H, as in the source. -/
inductive AmbientCases (hLH : L ≤ H) (R : Subgroup H) (P : Sylow 2 H)
    (e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Prop
  | one (block : ChapterC.IsSL3EvenBlock (L.subgroupOf H) 1)
      (natural : Nonempty (LayerModel L (commutatorCore L) ⊥
        (ambientMarking hLH e) (NaturalCopies (ZMod 2) 1)))
  | two (natural : Nonempty (LayerModel L (commutatorCore L) ⊥
        (ambientMarking hLH e) (NaturalCopies (ZMod 2) 2)))
      (radical : RadicalInequality R P)
  | three (natural : Nonempty (LayerModel L (coreCenter L) ⊥
        (ambientMarking hLH e) (NaturalCopies (ZMod 2) 1)))
      (dual : Nonempty (LayerModel L (commutatorCore L) (coreCenter L)
        (ambientMarking hLH e) (DualCopies (ZMod 2) 2)))
      (radical : RadicalInequality R P)
  | five (binary_quotient : Nonempty ((L ⧸ pCore 2 L) ≃*
        CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Natural.Actor))
      (fixed_order : Nat.card (coreFixed L) = 2)
      (natural : Nonempty (LayerModel L (commutatorCore L) (coreFixed L)
        (ambientMarking hLH e) (NaturalCopies (ZMod 2) 1)))
      (central_omega : Stellmacher.omegaOneCenterAmbient (P : Subgroup H) ≤ center H)
      (radical : IndexSevenPointRadical (L.subgroupOf H) R P)

/-- Transport every surviving layer and retain every other source clause. -/
theorem ambientCases_of_survivors [Finite G] (hLH : L ≤ H)
    (hcomp : (L.subgroupOf H).IsCComponent) {R : Subgroup H} {P : Sylow 2 H}
    {e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (h : FirstThreeCases (L.subgroupOf H) R P e ∨ FifthCase (L.subgroupOf H) R P e) :
    AmbientCases hLH R P e := by
  rcases h with h | h
  · cases h with
    | one hb hm =>
      obtain ⟨m⟩ := hm
      have hm := ambientLayer hLH m
      rw [sourceQ_map_subtype hLH hcomp, Subgroup.map_bot] at hm
      exact .one hb ⟨hm⟩
    | two hm hr =>
      obtain ⟨m⟩ := hm
      have hm := ambientLayer hLH m
      rw [sourceQ_map_subtype hLH hcomp, Subgroup.map_bot] at hm
      exact .two ⟨hm⟩ hr
    | three hn hd hr =>
      obtain ⟨n⟩ := hn
      obtain ⟨m⟩ := hd
      have hn := ambientLayer hLH n
      have hm := ambientLayer hLH m
      rw [sourceCenter_map_subtype hLH hcomp, Subgroup.map_bot] at hn
      rw [sourceQ_map_subtype hLH hcomp, sourceCenter_map_subtype hLH hcomp] at hm
      exact .three ⟨hn⟩ ⟨hm⟩ hr
  · obtain ⟨m⟩ := h.natural
    have hm := ambientLayer hLH m
    rw [sourceQ_map_subtype hLH hcomp, sourceFixed_map hLH hcomp] at hm
    have hc : Nat.card (coreFixed L) = 2 := by
      rw [← sourceFixed_map hLH hcomp, card_map_of_injective H.subtype_injective]
      exact h.fixed_order
    exact .five ⟨(quotientComparison hLH).symm.trans h.binary_quotient.some⟩
      hc ⟨hm⟩ h.central_omega h.radical

/-- Eliminate the fourth case after the two ambient action obligations are proved.
Both the complete local result and its compatible ambient layers are returned. -/
theorem survivors_of_ambient_control [Finite G] (d : LocalData G)
    (hLH : L ≤ H) (hcomp : (L.subgroupOf H).IsCComponent)
    (R : Subgroup H) (P : Sylow 2 H)
    (e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcore : L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (hSL : d.S ≤ normalizer (L : Set G))
    (hSC : FourthCase (L.subgroupOf H) R P e →
      d.S ≤ centralizer (coreFixed L : Set G))
    (h : Alternatives (ZMod 2) 1 (L.subgroupOf H) R P e) :
    (FirstThreeCases (L.subgroupOf H) R P e ∨ FifthCase (L.subgroupOf H) R P e) ∧
      AmbientCases hLH R P e := by
  have hout : FirstThreeCases (L.subgroupOf H) R P e ∨ FifthCase (L.subgroupOf H) R P e := by
    cases h with
    | one hb hn => exact Or.inl (.one hb hn)
    | two hn hr => exact Or.inl (.two hn hr)
    | three hn hd hr => exact Or.inl (.three hn hd hr)
    | four he hc hz hCZ hUZ hs hn hfd hcd hun hr =>
      have hf : FourthCase (L.subgroupOf H) R P e :=
        ⟨he, hc, hz, hCZ, hUZ, hs, hn, hfd, hcd, hun, hr⟩
      exact (fourthCase_impossible_of_ambient_action d hLH hcomp R P e hf
        hcore hR hindex hZ hZS hSL (hSC hf)).elim
    | five hb hc hn hz hr => exact Or.inr ⟨hb, hc, hn, hz, hr⟩
  exact ⟨hout, ambientCases_of_survivors hLH hcomp hout⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases
end
