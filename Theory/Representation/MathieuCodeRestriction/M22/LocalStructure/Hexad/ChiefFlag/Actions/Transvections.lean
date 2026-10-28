module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Inputs
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Faithfulness

/-!
# Full hexad transvections and the dual conjugation section

Inverse duality sends the full axis radical on cocode/U to a full center
radical on V5. Its center lies in the actual kernel fixed space; their common
dimension one identifies it with V1. Restriction of the coordinate pairing
then constructs V5/V1 as the dual of the kernel conjugation module. Every
map retains its literal stabilizer action.

Source: Aschbacher--Smith H.15.2(6) and H.16.4(2), printed pp.399,403,
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
namespace MathieuCode.Hexad.ChiefFlag.Actions
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The actual fixed line inside the actual commutator space. -/
def codeCenter : Subrepresentation V5.toRepresentation where
  toSubmodule := V1.toSubmodule.comap V5.toSubmodule.subtype
  apply_mem_toSubmodule g _ hv := V1.apply_mem_toSubmodule g hv

def fiveDualEquiv : Module.Dual (ZMod 2) (M22Cocode ⧸ U.toSubmodule) ≃ₗ[ZMod 2]
    V5.toSubmodule := quotientDualAnnihilatorEquiv U.toSubmodule

theorem fiveDualEquiv_equivariant (g : Stabilizer)
    (f : Module.Dual (ZMod 2) (M22Cocode ⧸ U.toSubmodule)) :
    fiveDualEquiv (U.quotientRepresentation.dual g f) = V5.toRepresentation g (fiveDualEquiv f) :=
  quotientDualAnnihilatorEquiv_equivariant Stabilizer U g f

theorem fiveDualEquiv_symm_equivariant (g : Stabilizer) (v : V5.toSubmodule) :
    fiveDualEquiv.symm (V5.toRepresentation g v) =
      U.quotientRepresentation.dual g (fiveDualEquiv.symm v) := by
  apply fiveDualEquiv.injective
  exact (fiveDualEquiv.apply_symm_apply _).trans
    ((fiveDualEquiv_equivariant g (fiveDualEquiv.symm v)).trans
      (congrArg (V5.toRepresentation g) (fiveDualEquiv.apply_symm_apply v))).symm

theorem codeCenter_finrank (h : OuterRestrictionInput m22SourceOctad)
    (h24 : AmbientFixedInput m22SourceOctad) :
    Module.finrank (ZMod 2) codeCenter.toSubmodule = 1 := by
  have hl : V1.toSubmodule ≤ V5.toSubmodule := by
    rw [codeCommutatorSubrepresentation_space]
    exact codeFixed_le_commutator h h24
  rw [show codeCenter.toSubmodule = V1.toSubmodule.comap V5.toSubmodule.subtype from rfl,
    (Submodule.comapSubtypeEquivOfLe hl).finrank_eq]
  exact codeFixedSubrepresentation_finrank h

namespace CocodeActionData

theorem axis_finrank (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    Module.finrank (ZMod 2) D.axis.toSubmodule = 4 := by
  have hn := h.kernel_ne_bot h24.fixed_finrank
  obtain ⟨a, ha, ha1⟩ := (Kernel.bot_or_exists_ne_one).resolve_left hn
  have hl : U.toSubmodule ≤ fixedSpaceSpan m22OuterCocodeRepresentation Kernel := by
    intro v hv
    apply fixedSpace_le_fixedSpaceSpan m22OuterCocodeRepresentation ha ha1
    exact (mem_fixedSpace_zpowers_iff _ a v).mpr (hv ⟨a, ha⟩)
  have hxi := h.xi_hyperplane h24.displacement h24.xi_codim hn
  have hdim := (fixedSpaceSpan m22OuterCocodeRepresentation Kernel).finrank_quotient_add_finrank
  have hU : Module.finrank (ZMod 2) U.toSubmodule = 5 :=
    h.fixedSpace_finrank h24.displacement h24.fixed_finrank
  have hm := HexadTransfer.finrank_map_add_ker U.toSubmodule.mkQ
    (fixedSpaceSpan m22OuterCocodeRepresentation Kernel)
    (by rw [Submodule.ker_mkQ]; exact hl)
  rw [Submodule.ker_mkQ, hU] at hm
  change Module.finrank (ZMod 2) cocodeAxis + 5 = _ at hm
  rw [finrank_m22Cocode] at hdim
  change Module.finrank (ZMod 2)
    (M22Cocode ⧸ fixedSpaceSpan m22OuterCocodeRepresentation Kernel) = 1 at hxi
  rw [hxi] at hdim
  rw [D.axis_space]
  omega

def dualCenter (D : CocodeActionData E) : Submodule (ZMod 2) V5.toSubmodule :=
  D.axis.toSubmodule.dualAnnihilator.map fiveDualEquiv.toLinearMap

theorem dualCenter_finrank (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    Module.finrank (ZMod 2) D.dualCenter = 1 := by
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq D.axis.toSubmodule
  have hU : Module.finrank (ZMod 2) U.toSubmodule = 5 :=
    h.fixedSpace_finrank h24.displacement h24.fixed_finrank
  have hQ := U.toSubmodule.finrank_quotient_add_finrank
  rw [hU, finrank_m22Cocode] at hQ
  rw [D.axis_finrank h h24] at hd
  change Module.finrank (ZMod 2)
    (D.axis.toSubmodule.dualAnnihilator.map fiveDualEquiv.toLinearMap) = 1
  rw [LinearEquiv.finrank_map_eq]
  omega

theorem codeAction_full_dualCenter (D : CocodeActionData E) :
    codeKernelAction.range = BinaryLinear.radical D.dualCenter := by
  exact dualAction_full cocodeKernelAction codeKernelAction D.axis.toSubmodule fiveDualEquiv
    (fun g f => fiveDualEquiv_equivariant (kernelInclusion g) f) D.axisAction_full

theorem dualCenter_le_codeCenter (D : CocodeActionData E) :
    D.dualCenter ≤ codeCenter.toSubmodule := by
  intro v hv g
  have hg : codeKernelAction g ∈ BinaryLinear.radical D.dualCenter := by
    rw [← D.codeAction_full_dualCenter]
    exact ⟨g, rfl⟩
  exact congrArg Subtype.val (hg.1 v hv)

/-- The transvection center is the actual fixed line, not a chosen line. -/
theorem dualCenter_eq_codeCenter (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    D.dualCenter = codeCenter.toSubmodule :=
  Submodule.eq_of_le_of_finrank_eq D.dualCenter_le_codeCenter
    ((D.dualCenter_finrank h h24).trans (codeCenter_finrank h h24).symm)

/-- The actual kernel induces the full group of transvections centered on V1. -/
theorem codeAction_full (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    codeKernelAction.range = BinaryLinear.radical codeCenter.toSubmodule := by
  rw [D.codeAction_full_dualCenter, D.dualCenter_eq_codeCenter h h24]

/-- Fullness and the genuine axis/kernel marking already force faithfulness. -/
theorem axisAction_faithful (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    Function.Injective cocodeKernelAction := by
  have hQ := U.toSubmodule.finrank_quotient_add_finrank
  have hU : Module.finrank (ZMod 2) U.toSubmodule = 5 :=
    h.fixedSpace_finrank h24.displacement h24.fixed_finrank
  rw [hU, finrank_m22Cocode] at hQ
  have hp : D.axis.toSubmodule ≠ ⊤ := by
    intro he
    have hd := D.axis_finrank h h24
    rw [he, finrank_top] at hd
    omega
  exact faithful_of_full_radical cocodeKernelAction D.axis.toSubmodule hp
    ((D.axisEquiv.toEquiv.trans (Multiplicative.ofAdd.trans D.kernelMarking.toEquiv)).symm)
    D.axisAction_full

theorem codeAction_faithful (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    Function.Injective codeKernelAction := by
  intro a b hab
  apply D.axisAction_faithful h h24
  apply BinaryTransvectionGroups.contragredient_injective
  apply LinearEquiv.ext
  intro f
  apply fiveDualEquiv.injective
  change fiveDualEquiv (U.quotientRepresentation.dual (kernelInclusion a) f) =
    fiveDualEquiv (U.quotientRepresentation.dual (kernelInclusion b) f)
  refine (fiveDualEquiv_equivariant (kernelInclusion a) f).trans (Eq.trans ?_
    (fiveDualEquiv_equivariant (kernelInclusion b) f).symm)
  exact congrArg (fun t : BinaryLinear.GL V5.toSubmodule => t (fiveDualEquiv f)) hab

theorem center_map_fiveDualEquiv (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    codeCenter.toSubmodule.map fiveDualEquiv.symm.toLinearMap = D.axis.toSubmodule.dualAnnihilator := by
  exact (Submodule.map_symm_eq_iff fiveDualEquiv).mpr (D.dualCenter_eq_codeCenter h h24)

/-- Restriction of the pairing to xi/U, followed by its conjugation marking,
gives the literal V5/V1 the dual kernel module. -/
def middleEquiv (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    (V5.toSubmodule ⧸ codeCenter.toSubmodule) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) E :=
  ((Submodule.Quotient.equiv codeCenter.toSubmodule D.axis.toSubmodule.dualAnnihilator
    fiveDualEquiv.symm (D.center_map_fiveDualEquiv h h24)).trans
    (Subspace.quotAnnihilatorEquiv D.axis.toSubmodule)).trans D.axisEquiv.symm.dualMap

theorem middleEquiv_mk (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (v : V5.toSubmodule) (w : E) :
    D.middleEquiv h h24 (codeCenter.toSubmodule.mkQ v) w =
      fiveDualEquiv.symm v (D.axisEquiv.symm w).val := rfl

theorem middleEquiv_equivariant (D : CocodeActionData E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (g : Stabilizer) (v : V5.toSubmodule ⧸ codeCenter.toSubmodule) :
    D.middleEquiv h h24 (codeCenter.quotientRepresentation g v) =
      D.kernelRepresentation.dual g (D.middleEquiv h h24 v) := by
  induction v using Submodule.Quotient.induction_on with | _ v =>
  apply LinearMap.ext
  intro w
  change fiveDualEquiv.symm (V5.toRepresentation g v) (D.axisEquiv.symm w).val =
    fiveDualEquiv.symm v (D.axisEquiv.symm (D.kernelRepresentation g⁻¹ w)).val
  refine (LinearMap.congr_fun (fiveDualEquiv_symm_equivariant g v)
    (D.axisEquiv.symm w).val).trans ?_
  change fiveDualEquiv.symm v (U.quotientRepresentation g⁻¹ (D.axisEquiv.symm w).val) = _
  congr 1
  have he := D.axisEquiv_equivariant g⁻¹ (D.axisEquiv.symm w)
  have he' := he.trans (congrArg (D.kernelRepresentation g⁻¹)
    (D.axisEquiv.apply_symm_apply w))
  exact congrArg Subtype.val ((D.axisEquiv.eq_symm_apply).mpr he')

end CocodeActionData
end MathieuCode.Hexad.ChiefFlag.Actions
