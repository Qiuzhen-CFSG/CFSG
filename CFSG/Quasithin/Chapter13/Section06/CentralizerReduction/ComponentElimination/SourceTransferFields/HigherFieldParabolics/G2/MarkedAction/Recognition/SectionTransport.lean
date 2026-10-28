module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection

/-!
# Reparametrizing the literal moved/fixed section

An equivalence of actors that leaves their action on the original vector space
unchanged identifies the moved spaces and then their fixed subspaces. Passing
the identity on those vectors to the quotients gives an action equivalence.
This is the transport from the nested component in the best-offender actor to
the original K⁺ in `Recognition.offenderSectionEquiv`.

Source: Aschbacher–Smith, B.5.1 and the paragraph before 13.6.14, printed
pp.99 and 929. These are quotient transport facts, not module recognition.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
open ChapterB.QuasisimpleSource
variable {D E V : Type*} [Group D] [Group E] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E V}
    (e : D ≃* E) (he : ∀ g v, ρ g v = σ (e g) v)

include e he in
private theorem reparametrize_moved : moved ρ ⊤ = moved σ ⊤ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, _, v, _, rfl⟩
    rw [he]
    exact Submodule.subset_span ⟨e d, mem_top _, v, Submodule.mem_top, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, _, v, _, rfl⟩
    obtain ⟨d, rfl⟩ := e.surjective a
    rw [← he]
    exact Submodule.subset_span ⟨d, mem_top _, v, Submodule.mem_top, rfl⟩

variable (s : MovedSection ρ ⊤) (t : MovedSection σ ⊤)

private def reparametrize_space : s.space.toSubmodule ≃ₗ[ZMod 2] t.space.toSubmodule where
  toFun x := ⟨x, (s.space_eq.trans ((reparametrize_moved e he).trans t.space_eq.symm)) ▸ x.property⟩
  invFun x := ⟨x, (t.space_eq.trans ((reparametrize_moved e he).symm.trans s.space_eq.symm)) ▸ x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem reparametrize_central :
    s.central.toSubmodule.map (reparametrize_space e he s t).toLinearMap = t.central.toSubmodule := by
  rw [s.central_eq, t.central_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ a
    obtain ⟨d, hd⟩ := e.surjective a.val
    apply Subtype.ext
    change σ a.val y.val = y.val
    rw [← hd, ← he]
    exact congrArg Subtype.val (hy ⟨d, mem_top _⟩)
  · intro hx
    refine ⟨(reparametrize_space e he s t).symm x, ?_, (reparametrize_space e he s t).apply_symm_apply x⟩
    intro d
    apply Subtype.ext
    change ρ d.val x.val = x.val
    rw [he]
    exact congrArg Subtype.val (hx ⟨e d.val, mem_top _⟩)

/-- Reparametrizing an actor transports its actual moved/fixed quotient.
The linear map is induced by the identity on the original vector space. -/
def reparametrizeMovedSection : ActionEquiv s.action t.action where
  groupEquiv := e
  linearEquiv := Submodule.Quotient.equiv _ _ (reparametrize_space e he s t)
    (reparametrize_central e he s t)
  intertwines g x := by
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    exact Subtype.ext (he g x.val)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
