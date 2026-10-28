module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.Inverter.Basic

/-!
# Assembly of the geometric five-inverter

A geometric seed and its noncentral action on CQ construct the literal
`FiveInverterData` consumed by the odd-core hyperplane argument. The square,
z-class, and quaternion conjugator are proved in `Inverter.Basic`.

This is a conditional assembly, not yet the inverter existence theorem of
J.2.7(5). The seed construction is owned by `qt-j127-five-inverter-seed`;
the no-transvection/J.2.4 noncentral-action argument is owned by
`qt-j127-five-inverter-action`. The final assembly owner
`qt-j127-five-inverter-source` must discharge both before claiming the
construction from LocalSetup, EarlierJ27Inputs and FiveQuaternionData alone.

Source: Aschbacher–Smith, J.2.7(5), printed p.436 (PDF p.447).
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  {B5 : Sylow 5 d.toTypeRuSetup.H}

/-- Apply the geometric seed to the exact inverter interface, constructing
the quaternion fusion witness from the action rather than assuming it. -/
def FiveInverterSeed.toData (v : FiveInverterSeed B5) (c : Choices d)
    (earlier : EarlierJ27Inputs c) (q : FiveQuaternionData B5)
    (hn : v.i ∉ centralizer (CQ B5 : Set G)) : FiveInverterData c B5 where
  i := v.i
  mem_H := v.mem_H
  square := v.square
  z_class := v.z_class c earlier
  inverts := v.inverts
  noncentral := hn
  fused := v.fused c q hn

/-- Conditional final assembly with both independent geometric obligations
visible. Their producers must discharge these premises at the source boundary. -/
theorem fiveInverterData_of_geometric_inputs (c : Choices d)
    (earlier : EarlierJ27Inputs c) (q : FiveQuaternionData B5)
    (hseed : Nonempty (FiveInverterSeed B5))
    (hact : ∀ v : FiveInverterSeed B5, v.i ∉ centralizer (CQ B5 : Set G)) :
    Nonempty (FiveInverterData c B5) := by
  obtain ⟨v⟩ := hseed
  exact ⟨v.toData c earlier q (hact v)⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
