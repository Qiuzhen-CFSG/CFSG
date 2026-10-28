module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.AlternatingFive
public import Theory.Representation.BinaryAlternatingFiveFlag.PlaneFixer
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Ambient

/-!
# Selecting the natural A₅ action in the original HS four-space

Deleted coordinates on the normal residual extend to the whole dotted
group through its exact linear normalizer. The five-point plane-fixer
calculation contradicts the original L₁ movement of the Sylow-fixed seed
point. The actual residual therefore has the natural SL₂(4) action.
This discharges the deleted alternative without assuming natural coordinates
or centerlessness. Centerlessness is used only in constructing the A₅
residual and its two possible modules.

NaturalOrder and FourCoordinates supply the ambient semilinear identification.
The higher-dimensional whole-component recognition remains an obligation
of this source task.
Source: Aschbacher--Smith 14.3.23(2) and 14.3.32, pp.1000,1003--1004.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem seed_stable (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (a : F.H) (ha : (a:G) ∈ normalizer (V : Set G)) (w : Additive F.Uhat)
    (hw : w ∈ hatSpace F V) :
    F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w ∈ hatSpace F V := by
  obtain ⟨b,hb,he⟩ := (show w.toMul ∈ hatImage F V from hw)
  refine ⟨F.uAction a b, (mem_normalizer_iff.mp ha (b:G)).mp hb, ?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction a b) = F.terminalHatAction a w.toMul
  change QuotientGroup.mk' (center F.U) (F.uAction a b) = F.uhatAction a w.toMul
  rw [← F.uhatAction_apply_mk,he]

variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

theorem source_no_deleted_five_coordinates
    (f : F.TerminalHdot →* Equiv.Perm (Fin 5))
    (hA : alternatingGroup (Fin 5) ≤ f.range)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (he : ∀ a w, c (F.terminalRepresentation a w) =
      BinaryPermutation.coreRepresentation (Fin 5) (f a) (c w)) : False := by
  let := chosen.elementary
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,_,B,v,hyp,hline,hfix⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  have hP : (P : Subgroup F.TerminalHdot) = F.terminalDot (T : Subgroup G) := rfl
  have hs : ∀ a∈P, ∀ w∈hatSpace F V, F.terminalRepresentation a w∈hatSpace F V := by
    rintro a ha w hw
    obtain ⟨b,hb,rfl⟩ := (show a∈F.terminalDot (T : Subgroup G) from hP ▸ ha)
    apply seed_stable F b _ w hw
    have hTV : (T : Subgroup G)≤normalizer (V : Set G) := by
      simpa only [F.last] using F.invariant 3
    exact hTV hb
  have hseed : hatSpace F (F.Vi 2) ≤ hatSpace F V := fun _ hw =>
    (show hatImage F (F.Vi 2)≤hatImage F V from map_mono (comap_mono (F.le_seed 2))) hw
  have hv : v∈hatSpace F V := hseed (hline ▸ Submodule.mem_span_singleton_self v)
  obtain ⟨k,hk,hm⟩ := source_seed_point_moved d earlier hq chosen F hne v hline
  apply hm
  apply BinaryPermutation.AlternatingFiveFlag.PlaneFixer.point_fixed_of_coordinates
    F.terminalRepresentation f hA c he P (hatSpace F V)
    (seed_hat_dimension F (source_closure d earlier hq chosen structural alternatives F hne).2.2)
    hs v hv (fun a ha => hfix a (hP ▸ ha)) k
  intro w hw
  obtain ⟨b,hb,rfl⟩ := hk
  exact seed_stable F b (chosen.normalizes (F.Li_le L 1 hb).1) w hw

/-- The normal residual cannot act as the deleted five-point module. -/
theorem source_four_residual_not_deleted
    (e : solvableResidual F.TerminalHdot ≃* alternatingGroup (Fin 5))
    (E : Representation.Equiv (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype)
      (OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp e.toMonoidHom)) :
    False := by
  obtain ⟨f,_,hf,hm⟩ := OrthogonalFourMinus.FivePoint.exists_ambient_permutation
    F.terminalRepresentation (solvableResidual F.TerminalHdot) e E.toLinearEquiv
    (fun a w => IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap a w) F.terminalRepresentation_injective
  have hA : alternatingGroup (Fin 5)≤f.range := by
    intro a ha
    obtain ⟨k,hk⟩ := e.surjective ⟨a,ha⟩
    exact ⟨k.val,(hm k).trans (congrArg Subtype.val hk)⟩
  let C := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let c := E.toLinearEquiv.trans C.symm
  apply source_no_deleted_five_coordinates d earlier hq chosen structural alternatives F hne f hA c
  intro a w
  apply C.injective
  change C (C.symm (E (F.terminalRepresentation a w))) =
    C (BinaryPermutation.coreRepresentation (Fin 5) (f a) (C.symm (E w)))
  rw [C.apply_symm_apply]
  change E.toLinearEquiv (F.terminalRepresentation a w) =
    C (BinaryPermutation.coreRepresentation (Fin 5) (f a) (C.symm (E.toLinearEquiv w)))
  rw [hf,BinaryPermutation.coreEquivNatural_equivariant,C.apply_symm_apply]

/-- Under centerlessness the exact residual has the natural SL₂(4) action. -/
theorem source_four_residual_natural
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4) :
    ∃ e : solvableResidual F.TerminalHdot ≃* SL(2,OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype)
        (SL2.BinarySmall.natural.comp e.toMonoidHom)) := by
  rcases source_four_residual_action_alternatives d earlier hq chosen structural alternatives
    F hne hZ hI hd with hn | ⟨e,⟨E⟩⟩
  · exact hn
  · exact (source_four_residual_not_deleted d earlier hq chosen structural alternatives F hne e E).elim

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
