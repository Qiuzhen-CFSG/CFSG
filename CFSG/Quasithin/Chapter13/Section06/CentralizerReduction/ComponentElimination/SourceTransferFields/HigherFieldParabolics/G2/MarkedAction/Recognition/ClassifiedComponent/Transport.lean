module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ModelContract
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.SectionTransport
public import Theory.Representation.G2NaturalTransitivity.FieldTransport

/-!
# Coefficient fields and the literal component section

An isomorphism of finite binary fields transports the actual octonion quotient
and its G₂ action. Restricting an ambient moved section to its defining subgroup
identifies it with every moved/fixed section of the restricted representation.
Both constructions retain the group map and a binary linear intertwiner.

These transports connect the surviving B.4.2 row to the component quotient in
the proof of Aschbacher–Smith 13.6.19 (printed pp.86, 99 and 931).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

def compose {D E H V W X : Type*} [Group D] [Group E] [Group H]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    {τ : Representation (ZMod 2) H X} (e : ActionEquiv ρ σ) (f : ActionEquiv σ τ) :
    ActionEquiv ρ τ where
  groupEquiv := e.groupEquiv.trans f.groupEquiv
  linearEquiv := e.linearEquiv.trans f.linearEquiv
  intertwines g v := by
    change f.linearEquiv (e.linearEquiv (ρ g v)) = _
    rw [e.intertwines, f.intertwines]
    rfl

def fieldActionEquiv {E F : BinaryField} (e : E.Carrier ≃+* F.Carrier) :
    ActionEquiv (binaryG2 E) (binaryG2 F) where
  groupEquiv := Atlas.G2.fieldEquiv e
  linearEquiv := LinearEquiv.ofBijective
    ((Atlas.G2.Natural.Transitivity.fieldTransport e).toAddEquiv.toAddMonoidHom.toZModLinearMap 2)
    (Atlas.G2.Natural.Transitivity.fieldTransport e).bijective
  intertwines := Atlas.G2.Natural.Transitivity.fieldTransport_action e

def sameFieldActionEquiv {E F : BinaryField} (h : Nat.card E.Carrier = Nat.card F.Carrier) :
    ActionEquiv (binaryG2 E) (binaryG2 F) := by
  let := Fintype.ofFinite E.Carrier
  let := Fintype.ofFinite F.Carrier
  exact fieldActionEquiv (FiniteField.ringEquivOfCardEq
    (by simpa only [← Nat.card_eq_fintype_card] using h))

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

def restrictedSection (s : MovedSection ρ C) : MovedSection (ρ.comp C.subtype) ⊤ where
  space := ⟨s.space.toSubmodule, fun c _ hv => s.space.apply_mem_toSubmodule c hv⟩
  space_eq := by
    rw [s.space_eq]
    apply congrArg (Submodule.span (ZMod 2))
    ext v
    constructor
    · rintro ⟨c, hc, w, hw, rfl⟩
      exact ⟨⟨c, hc⟩, mem_top _, w, hw, rfl⟩
    · rintro ⟨c, _, w, hw, rfl⟩
      exact ⟨c.val, c.property, w, hw, rfl⟩
  central := ⟨s.central.toSubmodule, fun c _ hv => s.central.apply_mem_toSubmodule c hv⟩
  central_eq := by
    rw [s.central_eq]
    ext x
    constructor
    · intro hx c
      exact hx c.val
    · intro hx c
      exact hx ⟨c, mem_top _⟩

def restrictSectionEquiv (s : MovedSection ρ C)
    (t : MovedSection (ρ.comp C.subtype) ⊤) :
    ActionEquiv t.action (s.action.comp C.subtype) :=
  reparametrizeMovedSection (MulEquiv.refl C) (fun _ _ => rfl) t (restrictedSection s)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent
