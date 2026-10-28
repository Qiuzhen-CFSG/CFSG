module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RadicalModule

/-!
# The source reflection moves the actual radical quotient

The reflection in R_j sends U_i to U_i^{s_j}. The first is disjoint from
V_i, the second lies in V_i, and the preceding commutator bound puts
V_j' inside V_i. Therefore a nonidentity element of U_i cannot have the
same image as its reflected element in V_j/V_j'. The actual descended
action, and hence its binary linear representation, is nontrivial.

This is the effective-action step needed before applying the representation
bounds in Fong--Seitz I (5D)--(5F) and (6E), printed pp.27--28 and44--45.
It uses the earlier root-reflection and local-kernel premises and the
abelianness of U_i. It does not assert faithfulness, irreducibility, or the
stronger local covering theorem of Section 5.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The source reflection genuinely moves the radical abelianization. -/
theorem radicalQuotientAction_reflection_ne_one (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (s : RootReflection Q split j) :
    radicalQuotientAction Q split j hKj ⟨s.val,s.mem_rankOne⟩ ≠ 1 := by
  intro he
  have heinv : radicalQuotientAction Q split j hKj (⟨s.val,s.mem_rankOne⟩ : rankOne Q split j)⁻¹ = 1 := by
    rw [map_inv, he, inv_one]
  have hDC : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ≤ simpleRemainder Q split i :=
    (radical_commutator_le_middle Q split hm i j hij hKi hA).trans
      (middleRoots_le_other_remainder Q split hm i j hij)
  have hEC : rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split i :=
    (show rootAt Q split i (Q.simple j) ≤ middleRoots Q split j i from
      le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm j i hij.symm)
  apply simpleRoot_ne_bot Q split i
  apply eq_bot_iff.mpr
  intro a ha
  let v : simpleRemainder Q split j := ⟨a,simpleRoot_le_other_remainder Q split hm i j hij ha⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  let v' := radicalAction Q split j hKj r⁻¹ v
  have hv' : (v' : X ⧸ Q.D) = (s.val : X ⧸ Q.D)⁻¹*a*(s.val : X ⧸ Q.D) :=
    radicalAction_right_conjugation Q split j hKj r v
  have hvE : (v' : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
    rw [rootAt_eq Q split i (Q.simple j) s.val s.class_eq, hv']
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*(s.val : X ⧸ Q.D))*
      (s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using ha
  have heq : Abelianization.of v' = Abelianization.of v := by
    rw [← radicalQuotientAction_of]
    change radicalQuotientAction Q split j hKj r⁻¹ (Abelianization.of v) = Abelianization.of v
    rw [heinv]
    rfl
  have hk : v⁻¹*v' ∈ (Abelianization.of : simpleRemainder Q split j →*
      RadicalQuotient Q split j).ker := by
    change Abelianization.of (v⁻¹*v') = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  have hdc : a⁻¹*(v' : X ⧸ Q.D) ∈ simpleRemainder Q split i := by
    apply hDC
    rw [← radicalProjection_kernel]
    exact mem_map_of_mem (simpleRemainder Q split j).subtype hk
  have haC : a ∈ simpleRemainder Q split i := by
    have ht := (simpleRemainder Q split i).mul_mem (hEC hvE) (inv_mem hdc)
    simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using ht
  exact mem_bot.mpr (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haC)

/-- The actual binary representation is nontrivial, witnessed by its source reflection. -/
theorem radicalRepresentation_reflection_ne_one (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (s : RootReflection Q split j)
    [IsElementaryAbelian 2 (RadicalQuotient Q split j)] :
    radicalRepresentation Q split j hKj ⟨s.val,s.mem_rankOne⟩ ≠ 1 := by
  intro he
  apply radicalQuotientAction_reflection_ne_one Q split hm i j hij hKi hKj hA s
  ext v
  induction v using QuotientGroup.induction_on with
  | H v =>
    have hv := congrArg (fun f : Module.End (ZMod 2) (Additive (RadicalQuotient Q split j)) =>
      f (Additive.ofMul (Abelianization.of v))) he
    rw [radicalRepresentation_of] at hv
    change Additive.ofMul (Abelianization.of (radicalAction Q split j hKj ⟨s.val,s.mem_rankOne⟩ v)) =
      Additive.ofMul (Abelianization.of v) at hv
    exact (radicalQuotientAction_of Q split j hKj ⟨s.val,s.mem_rankOne⟩ v).trans
      (Additive.ofMul.injective hv)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
