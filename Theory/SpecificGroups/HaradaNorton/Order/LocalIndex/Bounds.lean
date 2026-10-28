module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalSubgroup
public import Theory.GroupTheory.GeneratorCosetCoverIndex
public import Mathlib.GroupTheory.Index

/-!
# Independent bounds for the concrete Harada–Norton local index

A right coset cover supplies an upper bound; distinct translates of an object
fixed by the local subgroup supply a lower bound. No equality between the local
subgroup and a stabilizer is needed. Positive transitions suffice because the
ambient generators have orders dividing two and three.

Source for the actual subgroup words: ATLAS `HNG1-max1W1`, preserved in
`../source/`. The covering argument uses `GeneratorCosetCoverIndex`.
-/

namespace HaradaNorton.OrderCertificate

/-- The certified ambient generating pair. -/
@[expose] public def indexGenerator : Bool → HN
  | false => a
  | true => b

public theorem closure_range_indexGenerator :
    Subgroup.closure (Set.range indexGenerator) = ⊤ := by
  have hr : Set.range indexGenerator = ({a, b} : Set HN) := by
    ext x
    simp [indexGenerator]
  rw [hr]
  exact closure_generators

public noncomputable def indexCoverOfSteps {ι : Type*} (repr : ι → HN) (initial : ι)
    (hi : repr initial = 1)
    (step : ∀ i t, ∃ h : localSubgroup, ∃ j, repr i * indexGenerator t = h.val * repr j) :
    Subgroup.GeneratorCosetCover localSubgroup indexGenerator ι where
  repr := repr
  initial := initial
  initial_eq := hi
  step := step
  inv_step := by
    intro i t
    cases t with
    | false =>
      have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using a_sq)
      simpa only [indexGenerator, ha] using step i false
    | true =>
      have hb : b⁻¹ = b * b := inv_eq_of_mul_eq_one_right (by
        simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using b_cube)
      obtain ⟨h, j, hj⟩ := step i true
      obtain ⟨k, l, hl⟩ := step j true
      refine ⟨h * k, l, ?_⟩
      change repr i * b⁻¹ = (h.val * k.val) * repr l
      change repr i * b = h.val * repr j at hj
      change repr j * b = k.val * repr l at hl
      rw [hb, ← mul_assoc, hj, mul_assoc, hl, ← mul_assoc]

public theorem localSubgroup_index_le_of_cover
    (C : Subgroup.GeneratorCosetCover localSubgroup indexGenerator (Fin 1140000)) :
    localSubgroup.index ≤ 1140000 := by
  simpa using C.index_le_card closure_range_indexGenerator

public theorem localSubgroup_index_ge_of_separation (r : Fin 1140000 → HN)
    (hsep : ∀ i j, r i * (r j)⁻¹ ∈ localSubgroup → i = j) :
    1140000 ≤ localSubgroup.index := by
  simpa using localSubgroup.card_le_index_of_rightCoset_separation r hsep

public theorem localSubgroup_le_stabilizer {X : Type*} [MulAction HN X] (x : X)
    (ha : a • x = x) (hb : localB • x = x) :
    localSubgroup ≤ MulAction.stabilizer HN x := by
  apply (Subgroup.closure_le _).mpr
  exact Set.pair_subset_iff.mpr ⟨ha, hb⟩

public theorem localSubgroup_index_ge_of_action {X : Type*} [MulAction HN X] (x : X)
    (ha : a • x = x) (hb : localB • x = x)
    (repr : Fin 1140000 → HN)
    (hinj : Function.Injective (fun i => repr i • x)) :
    1140000 ≤ localSubgroup.index := by
  let f : Fin 1140000 → MulAction.orbit HN x :=
    fun i => ⟨repr i • x, MulAction.mem_orbit x (repr i)⟩
  have hf : Function.Injective f := by
    intro i j h
    exact hinj (congrArg Subtype.val h)
  have : Finite (MulAction.orbit HN x) :=
    (Finite.finite_mulAction_orbit x).to_subtype
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin, Nat.card_coe_set_eq, ← MulAction.index_stabilizer] at hcard
  exact hcard.trans (Subgroup.index_antitone (localSubgroup_le_stabilizer x ha hb))

end HaradaNorton.OrderCertificate
