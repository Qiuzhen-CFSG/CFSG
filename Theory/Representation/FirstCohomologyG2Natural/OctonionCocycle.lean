module

public import Theory.Representation.G2Natural
public import Theory.Representation.FirstCohomologyCyclic

/-!
# An explicit nonzero class for the natural G₂ derived action

For a split octonion `x`, project `g x - x` from the trace-zero hyperplane
modulo the scalar identity line. This gives a cocycle for the six-dimensional
natural module of the actual commutator subgroup. A trace-one octonion gives a
nonprincipal cocycle: two explicit commutators force any octonion with zero
projected displacement to have trace zero. Six further coordinate tests show
that the displacement kernel is exactly the scalar line. Its image therefore
has dimension seven, and its classes span a nonzero line in first cohomology.

All coordinate arguments work in characteristic two, including the binary
field, without replacing G₂(2)' by the full group. Surjectivity onto all
cocycles is a separate mathematical obligation; this module does not assert it.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
I.1.6(5), printed p.408 / PDF p.419, citing Jones--Parshall (1976).
The split-octonion coordinates and root maps come from the attributed ATLAS
ports imported by `G2Natural`; no additional ATLAS source is copied here.
-/

@[expose] public section

open Atlas.SplitOctonion Representation.OneCohomology
namespace Atlas.G2.Natural
open scoped commutatorElement
open Explicit
variable (K : Type*) [Field K]

/-- A chosen trace-one octonion, lifting the trivial quotient of the ambient action. -/
def traceOne : Carrier K := ![0, 0, 0, 1, 0, 0, 0, 0]
@[simp] theorem trace_traceOne : trace (traceOne K) = 1 := by simp [trace, traceOne]

/-- Octonion displacement lies in the trace-zero hyperplane. -/
def displacement (g : Model K) : Carrier K →ₗ[K] TraceZero K :=
  ((ambient K g) - LinearMap.id).codRestrict (TraceZero K) (by
    intro x
    change traceLinearMap K (ambient K g x - x) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (automorphism_trace g x))

@[simp] theorem displacement_val (g : Model K) (x : Carrier K) :
    (displacement K g x).val = g.val x - x := rfl

variable [CharP K 2]

/-- Displacement of an octonion, projected into the natural module of the actual derived group. -/
def ambientCocycle : Carrier K →ₗ[K] cocycles (derivedAction K) where
  toFun x := ⟨fun g => mk K (displacement K g.val x), by
    intro g h
    change mk K (displacement K (g.val * h.val) x) =
      derivedAction K g (mk K (displacement K h.val x)) + mk K (displacement K g.val x)
    rw [derivedAction_mk, ← map_add]
    congr 1
    apply Subtype.ext
    change (ambient K (g.val * h.val)) x - x =
      ambient K g.val (ambient K h.val x - x) + (ambient K g.val x - x)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  map_add' x y := by
    apply Subtype.ext
    funext g
    exact map_add ((mk K).comp (displacement K g.val)) x y
  map_smul' a x := by
    apply Subtype.ext
    funext g
    exact map_smul ((mk K).comp (displacement K g.val)) a x

@[simp] theorem ambientCocycle_traceZero (x : TraceZero K) :
    ambientCocycle K x.val = principal (derivedAction K) (mk K x) := by
  apply Subtype.ext
  funext g
  change mk K (displacement K g.val x.val) = derivedAction K g (mk K x) - mk K x
  rw [derivedAction_mk, ← map_sub]
  rfl

/-- The extension cocycle obtained from a trace-one octonion. -/
def distinguishedCocycle : cocycles (derivedAction K) := ambientCocycle K (traceOne K)

/-- Two explicit commutators detect the trace of an octonion with zero displacement class. -/
theorem trace_eq_zero_of_ambientCocycle_eq_zero (x : Carrier K)
    (hx : ambientCocycle K x = 0) : trace x = 0 := by
  have h (g h : Model K) : ∃ a : K, a • unit = (⁅g, h⁆ : Model K).val x - x := by
    let t : commutator (Model K) := ⟨⁅g, h⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
    have he := congrArg (fun f : cocycles (derivedAction K) => f.val t) hx
    exact (mk_eq_zero_iff K _).mp he
  obtain ⟨a, ha⟩ := h (rootA 1) weylR
  obtain ⟨b, hb⟩ := h (rootD 1) weylS
  have h1 := congrFun ha 0
  have h2 := congrFun hb 1
  simp [commutatorElement_def, rootA, rootAEquiv, rootALinear, rootAApply,
    weylR, weylREquiv, weylRLinear, weylRApply, unit, CharTwo.neg_eq] at h1
  simp [commutatorElement_def, rootD, rootDEquiv, rootDLinear, rootDApply,
    weylS, weylSEquiv, weylSLinear, weylSApply, unit, CharTwo.neg_eq] at h2
  dsimp [trace]
  linear_combination h2 - h1 + CharTwo.add_self_eq_zero (x 4) +
    CharTwo.add_self_eq_zero (x 6) - CharTwo.add_self_eq_zero (x 7)
/-- The trace-one cocycle is nonprincipal, including for the binary derived group. -/
theorem distinguishedCocycle_nonprincipal :
    ¬ ∃ v, principal (derivedAction K) v = distinguishedCocycle K := by
  rintro ⟨v, hv⟩
  obtain ⟨x, rfl⟩ := mk_surjective K v
  have hz : ambientCocycle K (traceOne K - x.val) = 0 := by
    rw [map_sub, ambientCocycle_traceZero, hv]
    exact sub_self _
  have ht := trace_eq_zero_of_ambientCocycle_eq_zero K _ hz
  have he : trace (traceOne K - x.val) = 1 := by
    change traceLinearMap K (traceOne K - x.val) = 1
    rw [map_sub]
    change trace (traceOne K) - trace x.val = 1
    rw [trace_traceOne, (show trace x.val = 0 from x.property), sub_zero]
  exact one_ne_zero (he.symm.trans ht)

/-- Remove the trace-one component of an octonion. -/
def traceZeroPart (x : Carrier K) : TraceZero K :=
  ⟨x - trace x • traceOne K, by
    change traceLinearMap K (x - trace x • traceOne K) = 0
    rw [map_sub, map_smul]
    change trace x - trace x * trace (traceOne K) = 0
    rw [trace_traceOne, mul_one, sub_self]⟩

/-- Every ambient displacement is a scalar multiple of the distinguished cocycle plus a principal one. -/
theorem ambientCocycle_decomposition (x : Carrier K) :
    ambientCocycle K x = trace x • distinguishedCocycle K +
      principal (derivedAction K) (mk K (traceZeroPart K x)) := by
  rw [← ambientCocycle_traceZero]
  change ambientCocycle K x = trace x • ambientCocycle K (traceOne K) +
    ambientCocycle K (x - trace x • traceOne K)
  rw [map_sub, map_smul]
  abel

/-- The distinguished cocycle gives a nonzero first-cohomology class. -/
theorem distinguishedClass_ne_zero :
    classMap (derivedAction K) (distinguishedCocycle K) ≠ 0 := by
  intro h
  exact distinguishedCocycle_nonprincipal K ((classMap_eq_zero_iff _ _).mp h)
/-- Explicit commutators detect all six off-diagonal coordinates and the trace;
only scalar identities have zero displacement class. -/
theorem ambientCocycle_eq_zero_iff (x : Carrier K) :
    ambientCocycle K x = 0 ↔ ∃ a : K, a • unit = x := by
  constructor
  · intro hx
    have h (g h : Model K) : ∃ a : K, a • unit = (⁅g, h⁆ : Model K).val x - x := by
      let t : commutator (Model K) := ⟨⁅g, h⁆,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
      have he := congrArg (fun f : cocycles (derivedAction K) => f.val t) hx
      exact (mk_eq_zero_iff K _).mp he
    have ht := trace_eq_zero_of_ambientCocycle_eq_zero K x hx
    obtain ⟨a0, h0⟩ := h (rootF 1) weylS
    obtain ⟨a1, h1⟩ := h (rootE 1) weylR
    obtain ⟨a2, h2⟩ := h (rootB 1) weylS
    obtain ⟨a5, h5⟩ := h (rootC 1) (rootF 1)
    obtain ⟨a6, h6⟩ := h (rootB 1) (rootE 1)
    obtain ⟨a7, h7⟩ := h (rootA 1) weylR
    have e0 := congrFun h0 1
    have e1 := congrFun h1 2
    have e2 := congrFun h2 1
    have e5 := congrFun h5 0
    have e6 := congrFun h6 0
    have e7 := congrFun h7 1
    simp [commutatorElement_def, rootF, rootFEquiv, rootFLinear, rootFApply,
      weylS, weylSEquiv, weylSLinear, weylSApply, unit, CharTwo.neg_eq] at e0
    simp [commutatorElement_def, rootE, rootEEquiv, rootELinear, rootEApply,
      weylR, weylREquiv, weylRLinear, weylRApply, unit, CharTwo.neg_eq] at e1
    simp [commutatorElement_def, rootB, rootBEquiv, rootBLinear, rootBApply,
      weylS, weylSEquiv, weylSLinear, weylSApply, unit, CharTwo.neg_eq] at e2
    simp [commutatorElement_def, rootC, rootCEquiv, rootCLinear, rootCApply,
      rootF, rootFEquiv, rootFLinear, rootFApply, unit, CharTwo.neg_eq] at e5
    simp [commutatorElement_def, rootB, rootBEquiv, rootBLinear, rootBApply,
      rootE, rootEEquiv, rootELinear, rootEApply, unit, CharTwo.neg_eq] at e6
    simp [commutatorElement_def, rootA, rootAEquiv, rootALinear, rootAApply,
      weylR, weylREquiv, weylRLinear, weylRApply, unit, CharTwo.neg_eq] at e7
    have e5' : 0 = x 5 := by
      linear_combination e5 - CharTwo.add_self_eq_zero (x 1) -
        CharTwo.add_self_eq_zero (x 3) + CharTwo.add_self_eq_zero (x 4) -
        3 * CharTwo.add_self_eq_zero (x 5) + 2 * CharTwo.add_self_eq_zero (x 7)
    have e6' : 0 = x 6 := by
      linear_combination e6 - CharTwo.add_self_eq_zero (x 5) -
        2 * CharTwo.add_self_eq_zero (x 6)
    have e34 : x 3 = x 4 := by
      dsimp [trace] at ht
      linear_combination ht - CharTwo.add_self_eq_zero (x 4)
    refine ⟨x 3, ?_⟩
    ext i
    fin_cases i <;> simp [unit, ← e0, ← e1, ← e2, ← e5', ← e6', ← e7, e34]
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    funext g
    change mk K (displacement K g.val (a • unit)) = 0
    have hz : displacement K g.val (a • unit) = 0 := by
      apply Subtype.ext
      change g.val.val (a • unit) - a • unit = 0
      rw [map_smul, automorphism_unit, sub_self]
    rw [hz, map_zero]

/-- The kernel of octonion displacement is precisely the identity line. -/
theorem ker_ambientCocycle :
    (ambientCocycle K).ker = K ∙ (unit : Carrier K) := by
  ext x
  exact (ambientCocycle_eq_zero_iff K x).trans Submodule.mem_span_singleton.symm

/-- The ambient octonions supply seven independent dimensions of cocycles. -/
theorem finrank_range_ambientCocycle :
    Module.finrank K (ambientCocycle K).range = 7 := by
  have h := (ambientCocycle K).finrank_range_add_finrank_ker
  rw [ker_ambientCocycle, finrank_span_singleton unit_ne_zero, carrier_finrank] at h
  omega

/-- An upper bound from the cocycle equations suffices to show every cocycle is an octonion displacement. -/
theorem ambientCocycle_surjective_of_finrank_cocycles_le [Finite K]
    (h : Module.finrank K (cocycles (derivedAction K)) ≤ 7) :
    Function.Surjective (ambientCocycle K) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  exact h.trans (finrank_range_ambientCocycle K).ge

/-- Unconditional lower bound for the natural derived-group cohomology. -/
theorem one_le_finrank_H1 [Finite K] :
    1 ≤ Module.finrank K (H1 (derivedAction K)) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.toSpanSingleton K (H1 (derivedAction K))
      (classMap (derivedAction K) (distinguishedCocycle K)))
    (smul_left_injective K (distinguishedClass_ne_zero K))
  simpa using h

end Atlas.G2.Natural
