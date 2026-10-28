module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.G2
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.NaturalResidual
public import CFSG.Quasithin.ChapterG.Section11.FourNatural
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Order120

/-!
# Centerlessness for every nonsolvable original four-space

Embed the faithful four-dimensional hatted action in Sp₄(2) = S₆ using
its original preserved alternating form. If the image contains A₆, the
literal group is A₆ or S₆ and the established six-letter contradictions
apply. Otherwise its solvable residual is A₅. The original point-residual
movement excludes its deleted module, so it acts naturally over F₄.

The actual marked plane and elementary actor rule out order sixty. The
normalizer of the natural residual then identifies the full order-120
actor with S₅, to which the proved S₅ centerlessness branch applies.
The argument uses no prior centerlessness or natural-coordinate premise.
The exhaustive original-flag application is in Centerless.Exhaustion.

Source: Aschbacher--Smith 14.3.23(2),24--25,31, printed pp.1000--1003.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
local instance hsCenterlessFourNaturalAlgebra :
    Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private def concreteCoordinates : SL2FourNatural.V ≃ₗ[ZMod 2]
    (Fin 2 → OrthogonalFourMinus.FiniteModel.Field 1) where
  toFun v i := SL2FourNatural.fieldEquiv (v i)
  invFun v i := SL2FourNatural.fieldEquiv.symm (v i)
  left_inv v := by funext i; exact SL2FourNatural.fieldEquiv.symm_apply_apply _
  right_inv v := by funext i; exact SL2FourNatural.fieldEquiv.apply_symm_apply _
  map_add' v w := by funext i; exact map_add SL2FourNatural.fieldEquiv _ _
  map_smul' c v := by funext i; exact ZMod.map_smul SL2FourNatural.fieldEquiv c (v i)

variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
include d earlier hq chosen structural alternatives hne hZ

omit hZ in
private theorem original_five_coordinates
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (j : F.TerminalHdot →* Equiv.Perm (Fin 6)) (hj : Function.Injective j)
    (hs : ¬ Group.IsSolvable F.TerminalHdot) (ha : ¬ alternatingGroup (Fin 6) ≤ j.range) :
    ∃ (e : solvableResidual F.TerminalHdot ≃* SL2FourNatural.SL)
      (c : Additive F.Uhat ≃ₗ[ZMod 2] SL2FourNatural.V),
      ∀ a w, c (F.terminalRepresentation a.val w)=SL2FourNatural.action (e a) (c w) := by
  rcases FourResidual.action_alternatives F.terminalRepresentation F.terminalRepresentation_injective
    hd j hj hs ha with ⟨e,⟨E⟩⟩ | ⟨e,⟨E⟩⟩
  · let e' := e.trans SL2FourNatural.standardGroupEquiv.symm
    let c := E.toLinearEquiv.trans concreteCoordinates.symm
    refine ⟨e',c,?_⟩
    intro a w
    have hi := IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap a w
    change E (F.terminalRepresentation a.val w) = specialLinearNatural 2 (e a) (E w) at hi
    apply concreteCoordinates.injective
    change concreteCoordinates (concreteCoordinates.symm (E (F.terminalRepresentation a.val w))) =
      concreteCoordinates (SL2FourNatural.action (e' a) (c w))
    rw [concreteCoordinates.apply_symm_apply]
    change _ = SL2FourNatural.standardVectorEquiv (SL2FourNatural.action (e' a) (c w))
    rw [SL2FourNatural.standard_equivariant]
    change _ = specialLinearNatural 2 (SL2FourNatural.standardGroupEquiv
      (SL2FourNatural.standardGroupEquiv.symm (e a)))
      (concreteCoordinates (concreteCoordinates.symm (E w)))
    rw [SL2FourNatural.standardGroupEquiv.apply_symm_apply,concreteCoordinates.apply_symm_apply]
    exact hi
  · exact (source_four_residual_not_deleted d earlier hq chosen structural alternatives F hne e E).elim

private theorem original_symmetricFive_model
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (j : F.TerminalHdot →* Equiv.Perm (Fin 6)) (hj : Function.Injective j)
    (hs : ¬ Group.IsSolvable F.TerminalHdot) (ha : ¬ alternatingGroup (Fin 6) ≤ j.range) :
    Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨e,c,he⟩ := original_five_coordinates d earlier hq chosen structural alternatives F hne hd j hj hs ha
  have hc : Nat.card F.TerminalHdot = 120 := by
    rcases Theory.SpecificGroups.SymmetricSix.card_eq_sixty_or_oneTwenty j hj hs ha with h60 | h120
    · obtain ⟨eA⟩ := Theory.SpecificGroups.SymmetricSix.residual_equiv_alternatingFive j hj hs ha
      have hR : solvableResidual F.TerminalHdot = ⊤ := by
        apply eq_of_le_of_card_ge le_top
        rw [card_top,h60,Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      let R := solvableResidual F.TerminalHdot
      let eR : R ≃* F.TerminalHdot := MulEquiv.ofBijective R.subtype
        ⟨Subtype.val_injective, fun a => ⟨⟨a,by change a ∈ solvableResidual F.TerminalHdot; rw [hR]; exact mem_top a⟩,rfl⟩⟩
      have heR (a : F.TerminalHdot) : (eR.symm a).val=a := eR.apply_symm_apply a
      let e' := eR.symm.trans e
      have he' (a : F.TerminalHdot) (w : Additive F.Uhat) :
          c (F.terminalRepresentation a w)=SL2FourNatural.action (e' a) (c w) := by
        simpa only [e',MulEquiv.trans_apply,heR] using he (eR.symm a) w
      obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
      obtain ⟨_,heX,B,v,hyp,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
        d earlier hq chosen structural alternatives hne g hgP hgH
      let := heX
      have hb := source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
        F g hne hZ hgP hgH
      have hX : 4 ≤ Nat.card (F.terminalDot (F.X g)) := by
        have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
          (V := Additive (F.terminalDot (F.X g)))
        change Nat.card (F.terminalDot (F.X g)) = _ at hh
        rw [hh,Nat.card_zmod]
        exact Nat.pow_le_pow_right (by decide : 0<2)
          (by omega : 2≤finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))
      obtain ⟨_,_,hW,_⟩ := source_four_marked_geometry d earlier hq chosen structural alternatives
        F hne hd g hgP hgH
      exact (FourNatural.not_special_linear hyp hW hX e' c he').elim
    · exact h120
  obtain ⟨E,C,hE⟩ := SL2FourNatural.SemilinearNormalizer.coordinates_of_order_oneTwenty
    F.terminalRepresentation F.terminalRepresentation_injective hc
    (solvableResidual F.TerminalHdot) e c he
  exact ⟨E.trans SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv⟩

omit [Finite G] d earlier hq chosen structural alternatives [IsElementaryAbelian 2 F.Uhat] hne hZ in
private theorem model_of_alternatingSix_le {D : Type*} [Group D] [Finite D]
    (j : D →* Equiv.Perm (Fin 6)) (hj : Function.Injective j)
    (ha : alternatingGroup (Fin 6) ≤ j.range) :
    Nonempty (D ≃* alternatingGroup (Fin 6)) ∨ Nonempty (D ≃* Equiv.Perm (Fin 6)) := by
  have hD : j.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le ha
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hD with hi | hi
  · right
    exact ⟨(MonoidHom.ofInjective hj).trans
      ((MulEquiv.subgroupCongr (index_eq_one.mp hi)).trans Subgroup.topEquiv)⟩
  · left
    have he : alternatingGroup (Fin 6) = j.range := by
      apply eq_of_le_of_card_ge ha
      have hh := j.range.card_mul_index
      rw [hi,Nat.card_perm,Nat.card_fin] at hh
      norm_num [Nat.factorial] at hh
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
      omega
    exact ⟨(MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr he.symm)⟩

include classification in
/-- The original nonsolvable four-space implies centerlessness with all model choices discharged. -/
theorem source_centerless_of_nonsolvable_four
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (hs : ¬ Group.IsSolvable F.TerminalHdot) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,heX,B,v,hyp,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  obtain ⟨c,j,hj,he⟩ := exists_binarySymplecticFour_embedding F.terminalRepresentation
    hyp.faithful hd B hyp.alternating hyp.nondegenerate hyp.preserves
  let j' := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp j
  have hj' : Function.Injective j' :=
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.injective.comp hj
  have hc : Nat.card F.Uhat = 16 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    simpa only [Nat.card_zmod,hd,show (2 : ℕ)^4=16 by decide] using hh
  apply source_centerless_of_four_nonsolvable_model d earlier hq chosen structural alternatives
    F hne classification hZ hc
  by_cases ha : alternatingGroup (Fin 6) ≤ j'.range
  · exact .inr (model_of_alternatingSix_le j' hj' ha)
  · exact .inl (original_symmetricFive_model d earlier hq chosen structural alternatives F hne hZ hd j' hj' hs ha)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
