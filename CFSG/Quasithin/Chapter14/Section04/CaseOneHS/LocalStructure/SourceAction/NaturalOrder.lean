module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.NaturalResidual
public import CFSG.Quasithin.ChapterG.Section11.FourNatural
/-!
# The original natural four-space has an order-120 dotted actor

Transport the selected residual module into the concrete quadratic field.
If the whole dotted group had order sixty, its A₅ residual would be the
whole group. The original elementary actor has order at least four and
its invariant plane has only a one-dimensional fixed part. The natural
SL₂(4) Sylow-plane calculation contradicts this. The checked order
dichotomy therefore leaves order 120.

FourCoordinates extends these literal residual coordinates to the full
action and applies the original ActionStructure and LocalStructure consumers.
Source: Aschbacher--Smith 14.3.23(2)(ii), printed p.1000.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open SL2FourNatural
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private def concreteCoordinates : SL2FourNatural.V ≃ₗ[ZMod 2]
    (Fin 2 → OrthogonalFourMinus.FiniteModel.Field 1) where
  toFun v i := fieldEquiv (v i)
  invFun v i := fieldEquiv.symm (v i)
  left_inv v := by funext i; exact fieldEquiv.symm_apply_apply _
  right_inv v := by funext i; exact fieldEquiv.apply_symm_apply _
  map_add' v w := by funext i; exact map_add fieldEquiv _ _
  map_smul' c v := by funext i; exact ZMod.map_smul fieldEquiv c (v i)

variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
include d earlier hq chosen structural alternatives hne hZ hI

/-- Natural coordinates on the literal residual in the concrete field model. -/
theorem source_four_residual_concrete_coordinates
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4) :
    ∃ (e : solvableResidual F.TerminalHdot ≃* SL)
      (c : Additive F.Uhat ≃ₗ[ZMod 2] SL2FourNatural.V),
      ∀ a w, c (F.terminalRepresentation a.val w)=action (e a) (c w) := by
  obtain ⟨e,⟨E⟩⟩ := source_four_residual_natural d earlier hq chosen structural alternatives
    F hne hZ hI hd
  let e' := e.trans standardGroupEquiv.symm
  let c := E.toLinearEquiv.trans concreteCoordinates.symm
  refine ⟨e',c,?_⟩
  intro a w
  have hi := IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap a w
  change E (F.terminalRepresentation a.val w) = specialLinearNatural 2 (e a) (E w) at hi
  apply concreteCoordinates.injective
  change concreteCoordinates (concreteCoordinates.symm (E (F.terminalRepresentation a.val w))) =
    concreteCoordinates (action (e' a) (c w))
  rw [concreteCoordinates.apply_symm_apply]
  change _ = standardVectorEquiv (action (e' a) (c w))
  rw [standard_equivariant]
  change _ = specialLinearNatural 2 (standardGroupEquiv (standardGroupEquiv.symm (e a)))
    (concreteCoordinates (concreteCoordinates.symm (E w)))
  rw [standardGroupEquiv.apply_symm_apply,concreteCoordinates.apply_symm_apply]
  exact hi

theorem source_four_card_oneTwenty (hd : finrank (ZMod 2) (Additive F.Uhat)=4) :
    Nat.card F.TerminalHdot=120 := by
  have hc : Nat.card F.Uhat=16 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    simpa only [Nat.card_zmod,hd,show (2 : ℕ)^4=16 by decide] using hh
  rcases source_four_card_sixty_or_oneTwenty d earlier hq chosen structural alternatives
    F hne hZ hI hc with h60 | h120
  · exfalso
    obtain ⟨eA⟩ := source_four_residual_alternatingFive d earlier hq chosen structural alternatives
      F hne hZ hI hc
    have hR : solvableResidual F.TerminalHdot = ⊤ := by
      apply eq_of_le_of_card_ge le_top
      rw [card_top,h60,Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    let R := solvableResidual F.TerminalHdot
    let eR : R ≃* F.TerminalHdot := MulEquiv.ofBijective R.subtype
      ⟨Subtype.val_injective, fun a => ⟨⟨a,by change a ∈ solvableResidual F.TerminalHdot; rw [hR]; exact mem_top a⟩,rfl⟩⟩
    have heR (a : F.TerminalHdot) : (eR.symm a).val=a := eR.apply_symm_apply a
    obtain ⟨e,c,he⟩ := source_four_residual_concrete_coordinates d earlier hq chosen structural alternatives
      F hne hZ hI hd
    let e' := eR.symm.trans e
    have he' (a : F.TerminalHdot) (w : Additive F.Uhat) :
        c (F.terminalRepresentation a w)=action (e' a) (c w) := by
      simpa only [e',MulEquiv.trans_apply,heR] using he (eR.symm a) w
    let := chosen.elementary
    obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
    obtain ⟨heU,heX,B,v,hyp,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
      d earlier hq chosen structural alternatives hne g hgP hgH
    let := heX
    have hb := source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
      F g hne hZ hgP hgH
    have hX : 4≤Nat.card (F.terminalDot (F.X g)) := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := Additive (F.terminalDot (F.X g)))
      change Nat.card (F.terminalDot (F.X g)) = _ at hh
      rw [hh,Nat.card_zmod]
      exact Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))
    have hW : finrank (ZMod 2) (hatSpace F (F.E g))=2 := by
      rw [source_intersection_eq_seed_of_card_sixteen d earlier hq chosen structural alternatives
        F hne hI hc g hgP hgH]
      exact seed_hat_dimension F (source_closure d earlier hq chosen structural alternatives F hne).2.2
    exact ChapterG.Section11.FourNatural.not_special_linear hyp hW hX e' c he'
  · exact h120
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
