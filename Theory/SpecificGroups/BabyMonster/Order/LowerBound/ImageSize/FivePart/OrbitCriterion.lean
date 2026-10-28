module
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.Words
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Finite orbit certificates for the local five-part

Distinct points, generator transition permutations, and a spanning tree certify
an entire orbit. Its cardinality divides the order of the generated subgroup by
orbit–stabilizer. This uses no presentation or identification of that subgroup.
The decreasing tree supplies reachability; preservation under inverse generators
follows from surjectivity of the transition permutations.

The counting step is Mathlib's `MulAction.orbitEquivQuotientStabilizer` and
`Subgroup.card_quotient_dvd_card`.
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.FivePart
open scoped Pointwise

variable {G X J : Type*} [Group G] [MulAction G X]

/-- A decreasing tree in the generator transition graph proves reachability.
Only forward edges are needed, since a finite permutation orbit is strongly
connected under its generators. -/
theorem reachable_of_tree {n : ℕ} (g : J → G)
    (v : Fin n → X) (base : Fin n) (perm : J → Equiv.Perm (Fin n))
    (hstep : ∀ j i, g j • v i = v (perm j i))
    (parent : Fin n → Fin n) (edge : Fin n → J)
    (hlt : ∀ i, i ≠ base → (parent i).val < i.val)
    (hedge : ∀ i, i ≠ base → perm (edge i) (parent i) = i) :
    ∀ i, ∃ w : Subgroup.closure (Set.range g), w • v base = v i := by
  intro i
  induction i using (measure (fun i : Fin n => i.val)).wf.induction with
  | h i ih =>
    by_cases hi : i = base
    · subst i
      exact ⟨1, one_smul _ _⟩
    · obtain ⟨w, hw⟩ := ih (parent i) (hlt i hi)
      let s : Subgroup.closure (Set.range g) :=
        ⟨g (edge i), Subgroup.subset_closure ⟨edge i, rfl⟩⟩
      refine ⟨s * w, ?_⟩
      rw [mul_smul]
      change g (edge i) • (w • v base) = v i
      rw [hw, hstep, hedge i hi]

/-- A complete injective enumeration of an invariant transitive set certifies
a divisor of the actual generated subgroup order. -/
theorem enumeratedOrbit_card_dvd {n : ℕ} (g : J → G)
    (v : Fin n → X) (base : Fin n) (hv : Function.Injective v)
    (perm : J → Equiv.Perm (Fin n))
    (hstep : ∀ j i, g j • v i = v (perm j i))
    (hreach : ∀ i, ∃ w : Subgroup.closure (Set.range g), w • v base = v i) :
    n ∣ Nat.card (Subgroup.closure (Set.range g)) := by
  let H := Subgroup.closure (Set.range g)
  have hle : H ≤ MulAction.stabilizer G (Set.range v) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    change g j • Set.range v = Set.range v
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨perm j i, (hstep j i).symm⟩
    · rintro x ⟨i, rfl⟩
      refine ⟨v ((perm j).symm i), ⟨_, rfl⟩, ?_⟩
      simpa using hstep j ((perm j).symm i)
  have horbit : ∀ x : MulAction.orbit H (v base), x.val ∈ Set.range v := by
    rintro ⟨x, w, rfl⟩
    have hw := hle w.property
    rw [MulAction.mem_stabilizer_iff] at hw
    rw [← hw]
    exact ⟨v base, ⟨base, rfl⟩, rfl⟩
  let f : Fin n → MulAction.orbit H (v base) :=
    fun i => ⟨v i, hreach i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact hv (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi⟩ := horbit x
      exact ⟨i, Subtype.ext hi⟩
  have hc : Nat.card (MulAction.orbit H (v base)) = n := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fin]
  rw [← hc, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H (v base))]
  exact Subgroup.card_quotient_dvd_card _

end BabyMonster.OrderLowerBound.FivePart
