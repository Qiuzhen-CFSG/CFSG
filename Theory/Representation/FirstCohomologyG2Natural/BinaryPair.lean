module
public import Theory.Representation.FirstCohomologyG2Natural.OctonionCocycle
import Mathlib.Tactic.ReduceModChar
/-!
# Two explicit commutators for the binary natural G₂ action

The commutators `a = [C(1),S]` and `b = [R,S]` satisfy `b³ = 1` and
`babbaba = ababbab`. Off-diagonal octonion coordinates embed the natural
trace-zero quotient in six coordinates and give explicit formulas for both
actions. All identities hold over every field of characteristic two.
Generation of the binary derived subgroup is a separate assertion.

These are coordinate ingredients for Aschbacher--Smith, I.1.6(5),
printed p.408 / PDF p.419. Root and Weyl conventions come from the attributed
ATLAS ports imported by `OctonionCocycle`; no additional ATLAS source is copied.
-/

@[expose] public section
namespace Atlas.G2.Natural
open Atlas.SplitOctonion Explicit
open scoped commutatorElement
variable (K : Type*) [Field K] [CharP K 2]

/-- First explicit commutator, `[C(1),S]`. -/
def binaryA : commutator (Model K) :=
  ⟨⁅rootC 1, weylS⁆, Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
/-- Second explicit commutator, `[R,S]`. -/
def binaryB : commutator (Model K) :=
  ⟨⁅weylR, weylS⁆, Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _)⟩

/-- The six octonion coordinates outside the two diagonal entries. -/
def binaryOffDiagonal : Carrier K →ₗ[K] (Fin 6 → K) where
  toFun x := ![x 0,x 1,x 2,x 5,x 6,x 7]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl

omit [CharP K 2] in
@[simp] theorem binaryOffDiagonal_unit : binaryOffDiagonal K unit = 0 := by
  ext i; fin_cases i <;> simp [binaryOffDiagonal, unit]

/-- Off-diagonal coordinates descend through the scalar identity line. -/
def binaryCoordinates : Space K →ₗ[K] (Fin 6 → K) :=
  (scalarLine K).liftQ ((binaryOffDiagonal K).comp (TraceZero K).subtype) (by
    apply Submodule.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    change binaryOffDiagonal K unit = 0
    exact binaryOffDiagonal_unit K)

@[simp] theorem binaryCoordinates_mk (x : TraceZero K) :
    binaryCoordinates K (mk K x) = ![x.val 0,x.val 1,x.val 2,x.val 5,x.val 6,x.val 7] := rfl

theorem binaryCoordinates_injective : Function.Injective (binaryCoordinates K) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  obtain ⟨x,rfl⟩ := mk_surjective K v
  change binaryCoordinates K (mk K x) = 0 at hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  have h5 := congrFun hv 3
  have h6 := congrFun hv 4
  have h7 := congrFun hv 5
  simp only [binaryCoordinates_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Pi.zero_apply] at *
  have ht : x.val 3 = x.val 4 := by
    have hx : x.val 3 + x.val 4 = 0 := x.property
    linear_combination hx - CharTwo.add_self_eq_zero (x.val 4)
  exact (mk_eq_zero_iff K x).mpr ⟨x.val 3, by
    ext i
    fin_cases i <;> simp [unit, h0,h1,h2,h5,h6,h7,ht]⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem binaryA_apply (x : Carrier K) :
    (binaryA K).val.val x =
      ![x 0+x 2+x 3+x 4+x 7, x 1+x 3+x 4+x 5+x 6+x 7, x 2+x 6,
        x 3+x 6+x 7, x 4+x 6+x 7, x 5+x 7, x 6, x 7] := by
  ext i
  fin_cases i <;>
    simp [binaryA, commutatorElement_def, rootC, rootCEquiv, rootCLinear, rootCApply,
      weylS, weylSEquiv, weylSLinear, weylSApply, sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf
  all_goals reduce_mod_char!


theorem binaryB_apply (x : Carrier K) :
    (binaryB K).val.val x = ![x 5,x 7,x 1,x 3,x 4,x 6,x 0,x 2] := by
  ext i
  fin_cases i <;>
    simp [binaryB, commutatorElement_def, weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply, CharTwo.neg_eq]

/-- The order-three relation for the second commutator. -/
theorem binaryB_cube : binaryB K * (binaryB K * binaryB K) = 1 := by
  apply Subtype.ext
  apply Atlas.Algebra.MultiplicativeLinearAut.ext
  intro x
  change (binaryB K).val.val ((binaryB K).val.val ((binaryB K).val.val x)) = x
  simp only [binaryB_apply]
  ext i; fin_cases i <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- A short relation giving the remaining cocycle constraints. -/
theorem binary_pair_relation :
    binaryB K * (binaryA K * (binaryB K * (binaryB K * (binaryA K * (binaryB K * binaryA K))))) =
    binaryA K * (binaryB K * (binaryA K * (binaryB K * (binaryB K * (binaryA K * binaryB K))))) := by
  apply Subtype.ext
  apply Atlas.Algebra.MultiplicativeLinearAut.ext
  intro x
  change (binaryB K).val.val ((binaryA K).val.val ((binaryB K).val.val ((binaryB K).val.val
    ((binaryA K).val.val ((binaryB K).val.val ((binaryA K).val.val x)))))) =
    (binaryA K).val.val ((binaryB K).val.val ((binaryA K).val.val ((binaryB K).val.val
    ((binaryB K).val.val ((binaryA K).val.val ((binaryB K).val.val x))))))
  ext i
  fin_cases i <;> simp [binaryA_apply, binaryB_apply] <;> ring_nf
  all_goals reduce_mod_char!

/-- Action of the first commutator in off-diagonal coordinates. -/
theorem binaryCoordinates_binaryA (v : Space K) :
    binaryCoordinates K (derivedAction K (binaryA K) v) =
    ![binaryCoordinates K v 0 + binaryCoordinates K v 2 + binaryCoordinates K v 5,
      binaryCoordinates K v 1 + binaryCoordinates K v 3 + binaryCoordinates K v 4 + binaryCoordinates K v 5,
      binaryCoordinates K v 2 + binaryCoordinates K v 4,
      binaryCoordinates K v 3 + binaryCoordinates K v 5, binaryCoordinates K v 4, binaryCoordinates K v 5] := by
  obtain ⟨x,rfl⟩ := mk_surjective K v
  have ht : x.val 3 + x.val 4 = 0 := x.property
  rw [derivedAction_mk]
  change binaryOffDiagonal K ((binaryA K).val.val x.val) = _
  rw [binaryA_apply]
  ext i
  fin_cases i <;> simp [binaryOffDiagonal, binaryCoordinates_mk] <;> linear_combination ht

/-- Action of the second commutator in off-diagonal coordinates. -/
theorem binaryCoordinates_binaryB (v : Space K) :
    binaryCoordinates K (derivedAction K (binaryB K) v) =
    ![binaryCoordinates K v 3,binaryCoordinates K v 5,binaryCoordinates K v 1,
      binaryCoordinates K v 4,binaryCoordinates K v 0,binaryCoordinates K v 2] := by
  obtain ⟨x,rfl⟩ := mk_surjective K v
  rw [derivedAction_mk]
  change binaryOffDiagonal K ((binaryB K).val.val x.val) = _
  rw [binaryB_apply]
  rfl
end Atlas.G2.Natural
