module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.CoreCentrality
public import Theory.SpecificGroups.PSL3.OddDegreeCentralRecognition

/-!
# Lifting the odd-degree projective recognition to the full overcomponent

The actual common component is perfect and its two-core is central. After
recognizing its full central quotient as PSL₃(2ⁿ), odd n greater than one
makes its center trivial. The resulting marked SL₃ isomorphism supplies
the terminal model and proves the actual two-core trivial. A separate adapter
starts with the literal two-core quotient and proves that its kernel equals
the full center before applying the same cover result.

The projective recognition is still a premise, owned together with natural
marking and Hall placement by qt-d-10-nona5-moving-hall-three. These lemmas
remove the cover and core-triviality premises from that owner's Hall consumer.
Source: Aschbacher–Smith 10.2.3(4), printed p.747, using A.2.12(I), A.2.18
and I.1.3(2), printed pp.36,40 and407.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The recognized central quotient kills the whole center and two-core,
while preserving its projective marking. -/
theorem CommonOvercomponent.odd_center_quotient_recognition
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (hn : 1 < n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le)))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2^n)
    (e : c.overcomponent ⧸ center c.overcomponent ≃* PSL(3,F)) :
    center c.overcomponent = ⊥ ∧ pCore 2 c.overcomponent = ⊥ ∧
    ∃ j : SL(3,F) ≃* c.overcomponent,
      (e.toMonoidHom.comp (QuotientGroup.mk' (center c.overcomponent))).comp
        j.toMonoidHom = Matrix.PSL3.projection F := by
  let : IsQuasisimple c.overcomponent := c.quasisimple hi
  obtain ⟨hz,j,hj⟩ := Matrix.PSL3.OddDegreeCentralRecognition.marked_recognition hn ho hF e
  exact ⟨hz,bot_unique (hz ▸ c.twoCore_le_center hi),j,hj⟩

/-- The literal two-core quotient also suffices, with its marking preserved. -/
theorem CommonOvercomponent.odd_twoCore_quotient_recognition
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (hn : 1 < n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le)))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2^n)
    (e : c.overcomponent ⧸ pCore 2 c.overcomponent ≃* PSL(3,F)) :
    pCore 2 c.overcomponent = ⊥ ∧ center c.overcomponent = ⊥ ∧
    ∃ j : SL(3,F) ≃* c.overcomponent,
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.overcomponent))).comp
        j.toMonoidHom = Matrix.PSL3.projection F := by
  let : IsQuasisimple c.overcomponent := c.quasisimple hi
  exact Matrix.PSL3.OddDegreeCentralRecognition.central_quotient_marked_recognition
    hn ho hF (pCore 2 c.overcomponent) (c.twoCore_le_center hi) e

/-- The full central-quotient model supplies the actual terminal configuration. -/
theorem CommonOvercomponent.terminal_of_odd_center_quotient
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (hn : 1 < n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le)))
    (hm : ClassicalGroup.IsPSL (c.overcomponent ⧸ center c.overcomponent) 3 (2^n)) :
    center c.overcomponent = ⊥ ∧ pCore 2 c.overcomponent = ⊥ ∧
      Nonempty (TerminalConfiguration T L (B.map H.subtype) n) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨hz,hcore,j,_⟩ := c.odd_center_quotient_recognition hn ho hi hF e
  exact ⟨hz,hcore,c.terminal (.inl ⟨F,inferInstance,inferInstance,hF,⟨j.symm⟩⟩)⟩

/-- The two-core-quotient model supplies the actual terminal configuration. -/
theorem CommonOvercomponent.terminal_of_odd_twoCore_quotient
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (hn : 1 < n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le)))
    (hm : ClassicalGroup.IsPSL (c.overcomponent ⧸ pCore 2 c.overcomponent) 3 (2^n)) :
    pCore 2 c.overcomponent = ⊥ ∧ center c.overcomponent = ⊥ ∧
      Nonempty (TerminalConfiguration T L (B.map H.subtype) n) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨hcore,hz,j,_⟩ := c.odd_twoCore_quotient_recognition hn ho hi hF e
  exact ⟨hcore,hz,c.terminal (.inl ⟨F,inferInstance,inferInstance,hF,⟨j.symm⟩⟩)⟩
end CFSG.Quasithin.Chapter10.MovingHall
