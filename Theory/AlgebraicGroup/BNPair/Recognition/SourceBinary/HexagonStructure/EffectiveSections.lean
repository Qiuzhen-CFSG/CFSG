module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RadicalModule
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.Sections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LinearOdd

/-!
# Effective linear sections of the actual hexagon radical

If the constructed odd reflection--unipotent product moves a section,
its effective action is faithful: a nontrivial normal kernel would contain
the odd product, and the Frattini argument would force that product to act
trivially. This proves the linear instance of Fong--Seitz I (5D)(b).

For the whole radical U_sj = U ∩ K_j, root geometry supplies movement.
Trivial action of su would conjugate the opposite simple root U_i into
its disjoint radical, a contradiction. This is the linear (5F)(a) consumer.
It also makes the action on the actual radical abelianization faithful.
Fields of orders two and four are retained, with no perfectness premise.

Source: Fong--Seitz I (3G), (5D), (5F), printed pp.26--28; these are
effective-section inputs for (6E), not its mixed-commutator or irreducibility
conclusions. The nonlinear and solvable-supplement arguments remain separate.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
  (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
  (μ : localGroup Q split j ≃* PSL(2,F)) (s : RootReflection Q split j)

/-- The binary linear instance of (5D)(b), on any literal invariant section.
    The odd product is constructed above, and movement on M is the source
    premise. No effectiveness premise or unknown-group simplicity is used. -/
theorem linear_section_effectiveAction_injective (d : RootSection Q split j)
    (hmove : d.action (oddProduct Q split j hKj μ s) ≠ 1) :
    Function.Injective d.effectiveAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  by_contra hn
  have hc := linear_kernel_contains_oddProduct Q split j hKj μ s d.effectiveAction.ker hn
  exact hmove (d.action_eq_one_of_odd _ (oddProduct_order_coprime Q split j hKj μ s) hc)

theorem linear_section_effective (d : RootSection Q split j)
    (hmove : d.action (oddProduct Q split j hKj μ s) ≠ 1) : d.IsEffective := by
  unfold RootSection.IsEffective
  rw [(MonoidHom.ker_eq_bot_iff _).mpr
    (linear_section_effectiveAction_injective Q split j hKj μ s d hmove)]
  exact bot_le

/-- The whole actual radical, as the section U_sj/1. -/
@[expose] def radicalSection : RootSection Q split j where
  numerator := simpleRemainder Q split j
  le_radical := le_rfl
  normalized := (rankOne_le_parabolic Q split j).trans
    (remainder_parabolic_normalizes Q split j hKj)
  denominator := ⊥
  invariant _ := map_bot _

/-- This section is the source's literal U ∩ K_j. -/
theorem radicalSection_numerator :
    (radicalSection Q split j hKj).numerator = split.U ⊓ localKernel Q j :=
  remainder_eq_unipotent_inf_kernel Q split j hKj

@[simp] theorem radicalSection_numeratorAction_apply (r : rankOne Q split j)
    (x : simpleRemainder Q split j) :
    (radicalSection Q split j hKj).numeratorAction r x = radicalAction Q split j hKj r x := by
  exact Subtype.ext ((RootSection.numeratorAction_apply (radicalSection Q split j hKj) r x).trans
    (radicalAction_apply Q split j hKj r x).symm)

/-- Root movement (3G) forces the constructed odd product to move the whole
    actual radical. This does not rely on its abelianization moving. -/
theorem oddProduct_moves_radical (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i) :
    (radicalSection Q split j hKj).action (oddProduct Q split j hKj μ s) ≠ 1 := by
  intro he
  let d := radicalSection Q split j hKj
  let u := oddPartner Q split j hKj μ s
  have huU : (u : X ⧸ Q.D) ∈ split.U :=
    simpleRoot_le Q split j (oddPartner_mem_root Q split j hKj μ s)
  have huN : (u : X ⧸ Q.D) ∈ normalizer (simpleRemainder Q split i : Set _) :=
    remainder_parabolic_normalizes Q split i hKi
      (Q.tits.B_le_standardParabolic _ (split.U_le huU))
  apply simpleRoot_ne_bot Q split i
  apply eq_bot_iff.mpr
  intro a ha
  let x : d.numerator := ⟨a,simpleRoot_le_other_remainder Q split hm i j hij ha⟩
  have hx : d.numeratorAction (oddProduct Q split j hKj μ s) x = x := by
    have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x)) he
    rw [d.action_mk] at hh
    exact congrArg QuotientGroup.quotientBot hh
  have hx' : (s.val : X ⧸ Q.D)*(u : X ⧸ Q.D)*a*
      ((s.val : X ⧸ Q.D)*(u : X ⧸ Q.D))⁻¹ = a := by
    have hh := congrArg Subtype.val hx
    rw [d.numeratorAction_apply, oddProduct_coe] at hh
    exact hh
  have heq : (u : X ⧸ Q.D)*a*(u : X ⧸ Q.D)⁻¹ = (s.val : X ⧸ Q.D)⁻¹*a*s.val := by
    have ht := congrArg (fun z : X ⧸ Q.D => (s.val : X ⧸ Q.D)⁻¹*z*s.val) hx'
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using ht
  have hroot : (s.val : X ⧸ Q.D)⁻¹*a*s.val ∈ rootAt Q split i (Q.simple j) := by
    rw [rootAt_eq Q split i (Q.simple j) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using ha
  have hrootV : rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split i :=
    (show rootAt Q split i (Q.simple j) ≤ middleRoots Q split j i from
      le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm j i hij.symm)
  have haV : a ∈ simpleRemainder Q split i :=
    (mem_normalizer_iff.mp huN a).mpr (heq.symm ▸ hrootV hroot)
  exact mem_bot.mpr (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV)

include μ s

/-- The whole linear hexagon radical is effective in the exact sense of
    (5F)(a), including q=2 and q=4. -/
theorem linear_radical_effective (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i) :
    (radicalSection Q split j hKj).IsEffective :=
  linear_section_effective Q split j hKj μ s _
    (oddProduct_moves_radical Q split j hKj μ s hm i hij hKi)

theorem linear_radical_effectiveAction_injective (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i) :
    Function.Injective (radicalSection Q split j hKj).effectiveAction :=
  linear_section_effectiveAction_injective Q split j hKj μ s _
    (oddProduct_moves_radical Q split j hKj μ s hm i hij hKi)
/-- The effective Frattini action detects the action on the larger actual
    radical abelianization as well. -/
theorem linear_radicalQuotientAction_injective (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i) :
    Function.Injective (radicalQuotientAction Q split j hKj) := by
  intro r t he
  let d := radicalSection Q split j hKj
  apply linear_radical_effectiveAction_injective Q split j hKj μ s hm i hij hKi
  ext z
  induction z using QuotientGroup.induction_on with
  | H x =>
    rw [d.effectiveAction_mk, d.effectiveAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hh : Abelianization.of (radicalAction Q split j hKj r x) =
        Abelianization.of (radicalAction Q split j hKj t x) :=
      (radicalQuotientAction_of Q split j hKj r x).symm.trans
        ((congrArg (fun f : MulAut (RadicalQuotient Q split j) =>
          f (Abelianization.of (x : simpleRemainder Q split j))) he).trans
            (radicalQuotientAction_of Q split j hKj t x))
    have hd : radicalAction Q split j hKj r x / radicalAction Q split j hKj t x ∈
        commutator (simpleRemainder Q split j) := QuotientGroup.eq_iff_div_mem.mp hh
    let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
    apply (show frattini d.numerator ≤ d.effectiveDenominator from by
      rw [d.effectiveDenominator_eq]; exact le_sup_left)
    change (radicalSection Q split j hKj).numeratorAction r x /
      (radicalSection Q split j hKj).numeratorAction t x ∈ frattini d.numerator
    rw [radicalSection_numeratorAction_apply Q split j hKj r x,
      radicalSection_numeratorAction_apply Q split j hKj t x]
    exact commutator_le_frattini_of_isPGroup (p := 2) hd

/-- The faithful representation is on the same radical quotient used in 6E. -/
theorem linear_radicalRepresentation_injective (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    [IsElementaryAbelian 2 (RadicalQuotient Q split j)] :
    Function.Injective (radicalRepresentation Q split j hKj) := by
  intro r t he
  apply linear_radicalQuotientAction_injective Q split j hKj μ s hm i hij hKi
  ext v
  induction v using QuotientGroup.induction_on with
  | H x =>
    have hx := congrArg
      (fun f : Module.End (ZMod 2) (Additive (RadicalQuotient Q split j)) =>
        f (Additive.ofMul (Abelianization.of x))) he
    rw [radicalRepresentation_of, radicalRepresentation_of] at hx
    exact (radicalQuotientAction_of Q split j hKj r x).trans
      ((Additive.ofMul.injective hx).trans
        (radicalQuotientAction_of Q split j hKj t x).symm)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
