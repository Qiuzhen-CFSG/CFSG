module
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryHeldOrbits
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldConjugate
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryGlobal

/-!
# Excluding Held in the original ordinary triple-six point case

The unchanged whole-module image has order 16 or 32. Its original natural-action
orbit constraints and the native Held class counts force a pure sixteen-group.
The original perfect A5 actor supplies five in its normalizer, placing that
same image in a native elementary core. The actual section centralizer fixes
it, contradicting the literal cubic in that local overgroup.
Source: Aschbacher--Smith 12.7.5, printed p. 840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_point_ordinary_not_held_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G)))
    (hJ : IsComponent (centralizer ({(t : G)} : Set G)) J)
    (e : J ⧸ center J ≃* Held.He) : False := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let j := H.subtype.comp J.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center J))
  let E := (U.comap j).map q
  let B := (Lt.comap j).map q
  obtain ⟨hEa,hEc,hcomm,hEBcore⟩ :=
    original_tripleSix_ordinary_held_image h structural D a t ht heven J hJ e
  change IsElementaryAbelian 2 E at hEa
  let := hEa
  change Nat.card E = 16 ∨ Nat.card E = 32 at hEc
  change ⁅E,B⁆ = E at hcomm
  change E ≤ B.pCoreIn 2 at hEBcore
  have horbits := original_tripleSix_ordinary_held_involution_count h structural D a t ht heven J hJ e
  change (Nat.card E = 16 → 15 ∣ Nat.card {x : E // IsConj Held.a (x : Held.He)}) ∧
    (Nat.card E = 32 → Nat.card {x : E // IsConj Held.a (x : Held.He)} ≠ 6 ∧
      Nat.card {x : E // IsConj Held.a (x : Held.He)} ≠ 10) at horbits
  have h16 : Nat.card E = 16 := by
    rcases hEc with hh | hh
    · exact hh
    · rcases Held.OrdinaryElementary.card_classA_thirtyTwo E hh with h6 | h10
      · exact ((horbits.2 hh).1 h6).elim
      · exact ((horbits.2 hh).2 h10).elim
  have hpure : ∀ x : E, ¬ IsConj Held.a (x : Held.He) := by
    have hd := horbits.1 h16
    have hc := Held.OrdinaryElementary.card_classA_sixteen E h16
    have hz : Nat.card {x : E // IsConj Held.a (x : Held.He)} = 0 := by
      rcases hc with hc | hc | hc | hc | hc <;> omega
    intro x hx
    have hn : Nonempty {x : E // IsConj Held.a (x : Held.He)} := ⟨⟨x,hx⟩⟩
    have hpos : 0 < Nat.card {x : E // IsConj Held.a (x : Held.He)} := Nat.card_pos
    omega
  obtain ⟨hp,hb⟩ := original_tripleSix_ordinary_held_actor h structural D a t ht heven J hJ e
  change Group.IsPerfect B at hp
  let := hp
  change Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) at hb
  have hBN : B ≤ normalizer (E : Set Held.He) :=
    le_normalizer_iff_commutator_le_left.mpr hcomm.le
  have h5 : 5 ∣ Nat.card (normalizer (E : Set Held.He)) := by
    have hd := card_quotient_dvd_card (pCore 2 B)
    rw [Nat.card_congr hb.some.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hd
    exact (show 5 ∣ 60 by decide).trans (hd.trans (card_dvd_of_le hBN))
  obtain ⟨i,g,hEQ⟩ := Held.OrdinaryElementary.pure_sixteen_le_conjugate_core E h16 hpure h5
  have hfixed := original_tripleSix_ordinary_held_sectionCentralizer h structural D a t ht heven J hJ e
  exact ChapterC.OrdinaryPlacement.held_no_pure_sixteen_fixed_section
    B E h16 hpure (hEBcore.trans (pCoreIn_le 2 B)) hBN i g hEQ hfixed

end CFSG.Quasithin.Chapter12.Section07
