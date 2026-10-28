module

public import Theory.Representation.FirstCohomologyG2Natural.OctonionCocycle
public import Theory.Representation.FirstCohomologyG2Natural.BinaryPair
public import Theory.Representation.FirstCohomologyG2Natural.BinaryGeneration
import Mathlib.Tactic.ReduceModChar

/-!
# A cocycle bound from an explicit binary G₂ generating pair

For `a = [C(1),S]` and `b = [R,S]`, the relations `b³ = 1` and
`babbaba = ababbab` force five independent constraints on the twelve
coordinates of a cocycle's values at `a,b`. The first four coordinates at
`a` and the first three at `b` determine both values. A cocycle vanishing
on a generating set vanishes everywhere, so generation gives an injection
into `K⁷` and the desired dimension bound.

The calculation is uniform over characteristic two. The pair-generation
theorem discharges the generation premise over every field of order two,
giving the unconditional binary cocycle bound needed for Aschbacher--Smith,
I.1.6(5), printed p.408 / PDF p.419. The action is on the actual derived
subgroup throughout, and no cohomology bound is assumed.
-/

@[expose] public section

namespace Atlas.G2.Natural
variable (K : Type*) [Field K] [CharP K 2]

open Representation.OneCohomology

/-- Seven evaluations sufficient to determine a cocycle once the pair generates. -/
def binarySeven : cocycles (derivedAction K) →ₗ[K] (Fin 7 → K) where
  toFun f := ![binaryCoordinates K (f.val (binaryA K)) 0,
    binaryCoordinates K (f.val (binaryA K)) 1, binaryCoordinates K (f.val (binaryA K)) 2,
    binaryCoordinates K (f.val (binaryA K)) 3, binaryCoordinates K (f.val (binaryB K)) 0,
    binaryCoordinates K (f.val (binaryB K)) 1, binaryCoordinates K (f.val (binaryB K)) 2]
  map_add' f g := by ext i; fin_cases i <;> simp
  map_smul' r f := by ext i; fin_cases i <;> simp

private theorem cocycle_one (f : cocycles (derivedAction K)) : f.val 1 = 0 := by
  have h := f.property 1 1
  simpa using h.symm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The two displayed word relations force all omitted coordinates. -/
theorem binary_values_zero_of_seven (f : cocycles (derivedAction K))
    (hf : binarySeven K f = 0) : f.val (binaryA K) = 0 ∧ f.val (binaryB K) = 0 := by
  have ha0 := congrFun hf 0
  have ha1 := congrFun hf 1
  have ha2 := congrFun hf 2
  have ha3 := congrFun hf 3
  have hb0 := congrFun hf 4
  have hb1 := congrFun hf 5
  have hb2 := congrFun hf 6
  simp only [binarySeven, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at *
  have hmul (g h : commutator (Model K)) :
      f.val (g*h) = derivedAction K g (f.val h) + f.val g := f.property g h
  have hc := congrArg (fun g => binaryCoordinates K (f.val g)) (binaryB_cube K)
  have hr := congrArg (fun g => binaryCoordinates K (f.val g)) (binary_pair_relation K)
  simp only [hmul, map_add, binaryCoordinates_binaryA, binaryCoordinates_binaryB,
    cocycle_one, map_zero] at hc hr
  have hc0 := congrFun hc 0
  have hc1 := congrFun hc 1
  have hr0 := congrFun hr 0
  have hr4 := congrFun hr 4
  have hr5 := congrFun hr 5
  simp only [Pi.add_apply, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, ha0, ha1, ha2, ha3, hb0, hb1, hb2, zero_add, add_zero] at hc0 hc1 hr0 hr4 hr5
  have ha5 : binaryCoordinates K (f.val (binaryA K)) 5 = 0 := by
    linear_combination hr4
  have ha4 : binaryCoordinates K (f.val (binaryA K)) 4 = 0 := by
    rw [ha5] at hr5
    linear_combination hr5
  have hb5 : binaryCoordinates K (f.val (binaryB K)) 5 = 0 := by
    linear_combination hc1
  have hb4 : binaryCoordinates K (f.val (binaryB K)) 4 = 0 := by
    simp only [ha4, ha5, hb5, zero_add, add_zero] at hr0
    linear_combination (norm := (ring_nf; reduce_mod_char!)) hr0
  have hb3 : binaryCoordinates K (f.val (binaryB K)) 3 = 0 := by
    rw [hb4] at hc0
    linear_combination hc0
  constructor
  · apply binaryCoordinates_injective K
    ext i
    fin_cases i <;> simp [ha0,ha1,ha2,ha3,ha4,ha5]
  · apply binaryCoordinates_injective K
    ext i
    fin_cases i <;> simp [hb0,hb1,hb2,hb3,hb4,hb5]

/-- Cocycles are determined by their values on a generating pair. -/
theorem binarySeven_injective
    (hgen : Subgroup.closure ({binaryA K, binaryB K} : Set (commutator (Model K))) = ⊤) :
    Function.Injective (binarySeven K) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  obtain ⟨ha,hb⟩ := binary_values_zero_of_seven K f hf
  have hz (g : commutator (Model K))
      (hg : g ∈ Subgroup.closure ({binaryA K, binaryB K} : Set (commutator (Model K)))) :
      f.val g = 0 := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ha
      · exact hb
    | one => exact cocycle_one K f
    | mul g h _ _ hg hh => rw [f.property, hg, hh, map_zero, add_zero]
    | inv g _ hg =>
      have h := f.property g⁻¹ g
      simpa [hg, cocycle_one K f] using h.symm
  apply Subtype.ext
  funext g
  exact hz g (by rw [hgen]; trivial)

/-- Two certified relations give the seven-dimensional upper bound once the
explicit commutators are known to generate the actual derived subgroup. -/
theorem finrank_cocycles_le_seven_of_binary_generation
    (hgen : Subgroup.closure ({binaryA K, binaryB K} : Set (commutator (Model K))) = ⊤) :
    Module.finrank K (cocycles (derivedAction K)) ≤ 7 := by
  have h := LinearMap.finrank_le_finrank_of_injective (binarySeven_injective K hgen)
  simpa using h

/-- The natural action of the actual binary derived G₂ group has at most
seven dimensions of cocycles over every two-element field. -/
theorem finrank_cocycles_le_seven_binary [Finite K] (hK : Nat.card K = 2) :
    Module.finrank K (cocycles (derivedAction K)) ≤ 7 :=
  finrank_cocycles_le_seven_of_binary_generation K (binary_pair_generates K hK)

/-- The relation calculation exhausts cocycles by octonion displacements under
exactly the same group-generation hypothesis. -/
theorem ambientCocycle_surjective_of_binary_generation [Finite K]
    (hgen : Subgroup.closure ({binaryA K, binaryB K} : Set (commutator (Model K))) = ⊤) :
    Function.Surjective (ambientCocycle K) :=
  ambientCocycle_surjective_of_finrank_cocycles_le K
    (finrank_cocycles_le_seven_of_binary_generation K hgen)

end Atlas.G2.Natural
