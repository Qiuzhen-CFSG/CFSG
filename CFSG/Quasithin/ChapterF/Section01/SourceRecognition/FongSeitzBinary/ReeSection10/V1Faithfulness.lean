module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearActor

/-!
# Faithfulness of the literal V₁ action

The barred root coordinates distinguish the two endpoint images modulo X₁.
The unipotent partner fixes the shifted endpoint root, while the supplied
reflection carries it to the other endpoint. Their cubic product therefore
moves V₁. Every nontrivial normal kernel contains that cubic product, so
the actual rank-one conjugation action is faithful, including at q=2.
The pinned SL₂ representation retains the same quotient and source actor.

Source: Fong--Seitz I (5D), pp.26--27, and II p.222 before (10.6).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

theorem linearBarBoundary_product (a : positiveRoot Q split (.inr 2))
    (t : T1 Q split) (b : positiveRoot Q split (.inr 0)) :
    linearBarBoundary Q split c
      (inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) a *
       inclusion (T1_le_linearRemainder Q split c) t *
       inclusion (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)) b) =
      (positiveSuzukiBar Q split c 2 a,positiveSuzukiBar Q split c 0 b) := by
  unfold linearBarBoundary
  rw [MonoidHom.comp_apply,linearBoundary_product]
  rfl

theorem linearBarBoundary_left (a : positiveRoot Q split (.inr 2)) :
    linearBarBoundary Q split c
      (inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) a) =
      (positiveSuzukiBar Q split c 2 a,1) := by
  simpa only [map_one,mul_one] using linearBarBoundary_product Q split c a 1 1

theorem linearBarBoundary_right (b : positiveRoot Q split (.inr 0)) :
    linearBarBoundary Q split c
      (inclusion (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)) b) =
      (1,positiveSuzukiBar Q split c 0 b) := by
  simpa only [map_one,one_mul] using linearBarBoundary_product Q split c 1 1 b

include c in
/-- The cubic mover exchanges two different endpoint cosets, including q=2. -/
theorem V1_mover_moves : (V1Section Q split c).action (linearMover Q split c) ≠ 1 := by
  let s := (c.reflections 0).val
  let u := oddPartner Q split 0 (linearRemainder_le_kernel Q split c)
    (linearLocalMarking Q split c) (c.reflections 0)
  let A := positiveRoot Q split (.inr 2)
  let B := positiveRoot Q split (.inr 0)
  obtain ⟨a,ha⟩ := positiveSuzukiBar_surjective Q split c 2
    (Multiplicative.ofAdd (1 : ReeF4.CoefficientField m))
  have ha1 : positiveSuzukiBar Q split c 2 a ≠ 1 := by
    rw [ha]
    exact (one_ne_zero : (1 : ReeF4.CoefficientField m) ≠ 0)
  have hcomm : ⁅simpleRoot Q split 0,A⁆ = ⊥ :=
    adjacent_commutator_eq_bot Q split c.rotation_eight 0 1 (by decide)
      (linearRemainder_le_kernel Q split c) (remainder_le_kernel Q split c)
  have hu : (u : X ⧸ Q.D) ∈ simpleRoot Q split 0 :=
    oddPartner_mem_root Q split 0 (linearRemainder_le_kernel Q split c)
      (linearLocalMarking Q split c) (c.reflections 0)
  have huc : Commute (u : X ⧸ Q.D) (a : X ⧸ Q.D) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm hu) _ a.property).symm
  have hs : (s : X ⧸ Q.D)*(s : X ⧸ Q.D) = 1 := linearReflection_sq Q split c
  have hi : (s : X ⧸ Q.D)⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hAB : rightConjugate A (s : X ⧸ Q.D) = B := by
    change rightConjugate (rootAt Q split 1 (Q.simple 0)) (s : X ⧸ Q.D) = _
    rw [rootAt_right Q split 1 _ _ s (c.reflections 0).class_eq]
    have hh : Q.simple 0*Q.simple 0 = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 0)).2
    rw [hh,rootAt_one]
    simp only [B,positiveRoot,positiveKind,positiveWord,Matrix.cons_val_zero,rootAt_one]
  let y : B := ⟨(s : X ⧸ Q.D)*a*(s : X ⧸ Q.D)⁻¹,by
    rw [←hAB]
    change (s : X ⧸ Q.D)*((s : X ⧸ Q.D)*a*(s : X ⧸ Q.D)⁻¹)*
      (s : X ⧸ Q.D)⁻¹ ∈ A
    simpa only [hi,mul_assoc,←mul_assoc (s : X ⧸ Q.D) (s : X ⧸ Q.D),
      hs,one_mul,mul_one] using a.property⟩
  let v : (V1Section Q split c).numerator :=
    ⟨a,positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide) a.property⟩
  have hv : (V1Section Q split c).numeratorAction (linearMover Q split c) v =
      ⟨y,positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide) y.property⟩ := by
    apply Subtype.ext
    refine (RootSection.numeratorAction_apply (V1Section Q split c) (linearMover Q split c) v).trans ?_
    rw [show (linearMover Q split c : X ⧸ Q.D) = (s : X ⧸ Q.D)*u from
      oddProduct_coe Q split 0 (linearRemainder_le_kernel Q split c)
        (linearLocalMarking Q split c) (c.reflections 0)]
    dsimp only [v,y]
    calc
      _ = (s : X ⧸ Q.D)*((u : X ⧸ Q.D)*a*(u : X ⧸ Q.D)⁻¹)*
          (s : X ⧸ Q.D)⁻¹ := by simp only [mul_inv_rev,mul_assoc]
      _ = _ := by rw [huc.eq,mul_inv_cancel_right]
  intro he
  have heq := congrArg (fun f : MulAut (V1Section Q split c).Carrier =>
    V1BarEquiv Q split c (f (QuotientGroup.mk v))) he
  change V1BarEquiv Q split c (QuotientGroup.mk
    ((V1Section Q split c).numeratorAction (linearMover Q split c) v)) =
      V1BarEquiv Q split c (QuotientGroup.mk v) at heq
  rw [hv] at heq
  have hleft := (V1BarEquiv_mk Q split c
    (inclusion (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)) y)).trans
      (linearBarBoundary_right Q split c y)
  have hright := (V1BarEquiv_mk Q split c
    (inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) a)).trans
      (linearBarBoundary_left Q split c a)
  have heq' := hleft.symm.trans (heq.trans hright)
  exact ha1 (congrArg Prod.fst heq').symm

include c in
theorem V1_action_injective : Function.Injective (V1Section Q split c).action := by
  apply (V1Section Q split c).action.ker_eq_bot_iff.mp
  by_contra hn
  exact V1_mover_moves Q split c (linear_kernel_contains_oddProduct Q split 0
    (linearRemainder_le_kernel Q split c) (linearLocalMarking Q split c)
      (c.reflections 0) _ hn)

include c in
theorem V1Representation_injective : Function.Injective (V1Representation Q split c) := by
  intro r s he
  apply V1_action_injective Q split c
  ext v
  exact Additive.ofMul.injective (congrArg
    (fun f : Module.End (ZMod 2) (Additive (V1Section Q split c).Carrier) => f (Additive.ofMul v)) he)

/-- The faithful linear model acts on the literal quotient through the pinned source actor. -/
def linearV1Representation : Representation (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin 2) (ReeF4.CoefficientField m))
    (Additive (V1Section Q split c).Carrier) :=
  (V1Representation Q split c).comp (linearPinning Q split c).toMonoidHom

theorem linearV1Representation_injective : Function.Injective (linearV1Representation Q split c) :=
  (V1Representation_injective Q split c).comp (linearPinning Q split c).injective

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
