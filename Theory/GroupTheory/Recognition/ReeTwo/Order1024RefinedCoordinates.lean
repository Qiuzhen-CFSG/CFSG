module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedProfileCertificates
public import Theory.SpecificGroups.ReeTwo.SylowTailQuotient

/-!
# Quotient coordinates for the four refined-profile Ree two candidates

All four original subgroups are recovered as preimages of explicit
order-sixteen subgroups of the tail quotient. Short generator words prove
this equality; the coordinate equations alone would only give containment.
Three binary coordinate functions then give surjective homomorphisms to
`RefinedQuotient`, carrying the specified basis lifts to its standard basis.
Their Frattini-kernel identities and fiber counts are separate obligations.

For the first three cases the cyclic coordinate is even. For the last,
write `a = t mod 2` and `b = floor(t/2) mod 2`. The quotient coordinates
are `(b₃ + b + ab, b₂ + ab, a)`. The correction terms account for the
cyclic action and the convention that rootOne is the inverse generator.

Source: Shinoda (1975), (2.3), pp. 81–82; all formulas use the verified
multiplication and action of `SylowTailQuotient`. The generated word table
is checked by Lean's kernel and is used only to prove subgroup membership.
-/

namespace ReeTwo.SylowModel
open TailQuotient

@[expose] public def refinedGenerators (c : Fin 4) : Fin 4 → SylowModel :=
  ![![root 3, root 2, root 1, rootOne ^ 2 * root 0],
    ![root 2 * root 3, root 1 * root 3, root 0 * root 3, rootOne ^ 2 * root 3],
    ![root 2 * root 3, root 1 * root 3, root 0 * root 3, rootOne ^ 2],
    ![root 3, root 2, rootOne * root 0 * root 1, 1]] c

@[expose] public def refinedTailMember (c : Fin 4) (q : TailQuotient.Group) : Prop :=
  let a := q.left.toAdd 0
  let b := q.left.toAdd 1
  let d := q.left.toAdd 2
  let e := q.left.toAdd 3
  let t := q.right.toAdd.val
  match c.val with
  | 0 => t % 2 = 0 ∧ a = (t / 2 : ℕ)
  | 1 => t % 2 = 0 ∧ e = d + b + a + (t / 2 : ℕ)
  | 2 => t % 2 = 0 ∧ e = d + b + a
  | _ => a = (t : ℕ) ∧ b = (t : ℕ) + (t / 2 : ℕ)
public instance (c : Fin 4) (q : TailQuotient.Group) : Decidable (refinedTailMember c q) := by
  unfold refinedTailMember
  dsimp only
  split <;> infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
public theorem refinedTail_closed : ∀ c : Fin 4,
    refinedTailMember c 1 ∧
    (∀ x y, refinedTailMember c x → refinedTailMember c y → refinedTailMember c (x*y)) ∧
    (∀ x, refinedTailMember c x → refinedTailMember c x⁻¹) := by decide +kernel

@[expose] public def refinedCoordinates (c : Fin 4) (q : TailQuotient.Group) : RefinedQuotient :=
  let a : ZMod 2 := q.right.toAdd.val
  let b : ZMod 2 := (q.right.toAdd.val / 2 : ℕ)
  Multiplicative.ofAdd
    (![![q.left.toAdd 2 + q.left.toAdd 3, q.left.toAdd 1, q.left.toAdd 0],
       ![q.left.toAdd 1, q.left.toAdd 0, b],
       ![q.left.toAdd 1, q.left.toAdd 0, b],
       ![q.left.toAdd 3 + b + a*b, q.left.toAdd 2 + a*b, a]] c)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
public theorem refinedCoordinates_mul : ∀ c : Fin 4,
    refinedCoordinates c 1 = 1 ∧
    (∀ x y, refinedTailMember c x → refinedTailMember c y →
      refinedCoordinates c (x*y) = refinedCoordinates c x * refinedCoordinates c y) := by
  decide +kernel

public theorem refinedGenerators_tailMember : ∀ c j, refinedTailMember c (projection (refinedGenerators c j)) := by decide +kernel
@[expose] public def refinedBasisPosition (c : Fin 4) (j : Fin 3) : Fin 4 :=
  (![![0,2,3], ![1,2,3], ![1,2,3], ![0,1,2]] : Fin 4 → Fin 3 → Fin 4) c j
public theorem refinedCoordinates_basis : ∀ c : Fin 4, ∀ j : Fin 3,
  refinedCoordinates c (projection (refinedGenerators c (refinedBasisPosition c j))) = refinedBasis j := by decide +kernel

@[expose] public def refinedTailNode (c : Fin 4) : Subgroup TailQuotient.Group where
  carrier := refinedTailMember c
  one_mem' := (refinedTail_closed c).1
  mul_mem' := (refinedTail_closed c).2.1 _ _
  inv_mem' := (refinedTail_closed c).2.2 _

@[expose] public def refinedTailWord (c : Fin 4) (q : TailQuotient.Group) : List (Fin 4) :=
  ((#[[[], [], [2], [], [1], [], [2, 1], [], [0], [], [2, 0], [], [1, 0], [], [2, 1, 0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [3, 1, 0], [], [3, 2, 1, 0], [], [3, 0], [], [3, 2, 0], [], [3, 1], [], [3, 2, 1], [], [3], [], [3, 2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [2, 1], [], [2, 0], [1, 0], [], [], [2], [1], [], [0], [], [], [2, 1, 0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2, 3], [3, 1], [], [3, 0], [], [], [3, 2, 1], [3], [], [], [2, 3, 1], [], [3, 2], [3, 1, 0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [2, 1], [], [2, 0], [1, 0], [], [], [2], [1], [], [0], [], [], [2, 1, 0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [3], [], [], [2, 3, 1], [], [3, 2], [3, 1, 0], [], [], [2, 3], [3, 1], [], [3, 0], [], [], [3, 2, 1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []], [[], [], [], [], [1], [], [], [], [0], [], [], [], [1, 0], [], [], [], [], [], [], [2, 2, 2], [], [], [], [2, 2, 2, 1], [], [], [], [2, 2, 2, 0], [], [], [], [2, 2, 2, 1, 0], [], [], [2, 2, 0], [], [], [], [2, 2, 1, 0], [], [], [], [2, 2], [], [], [], [2, 2, 1], [], [], [2, 1], [], [], [], [2], [], [], [], [2, 1, 0], [], [], [], [2, 0], [], []]] : Array (List (List (Fin 4)))).getD c.val []).getD (coordinateCode q) []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
public theorem refinedTailWord_valid : ∀ c q, refinedTailMember c q →
  Theory.GroupTheory.evalWord (fun j => projection (refinedGenerators c j))
    (refinedTailWord c q) = q := by
  intro c q hq
  apply coordinateCode_injective
  exact (by decide +kernel : ∀ c q, refinedTailMember c q →
    coordinateCode (Theory.GroupTheory.evalWord (fun j => projection (refinedGenerators c j))
      (refinedTailWord c q)) = coordinateCode q) c q hq

private theorem refined_reverse_four (a b c d : SylowModel) :
    ({a,b,c,d} : Set SylowModel) = {d,c,b,a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto
private theorem refined_reverse_three (a b c : SylowModel) :
    ({a,b,c} : Set SylowModel) = {c,b,a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

public theorem refinedCandidate_eq_generated (c : Fin 4) :
    residualCandidate (refinedIndex c) = tailSubgroup ⊔
      Subgroup.closure (Set.range (refinedGenerators c)) := by
  fin_cases c <;>
    simp [residualCandidate, refinedIndex, refinedGenerators]
  · exact congrArg (fun s : Set SylowModel => tailSubgroup ⊔ Subgroup.closure s)
      (refined_reverse_four _ _ _ _)
  · exact congrArg (fun s : Set SylowModel => tailSubgroup ⊔ Subgroup.closure s)
      (refined_reverse_four _ _ _ _)
  · exact congrArg (fun s : Set SylowModel => tailSubgroup ⊔ Subgroup.closure s)
      (refined_reverse_four _ _ _ _)
  · exact congrArg (fun s : Set SylowModel => tailSubgroup ⊔ Subgroup.closure s)
      (refined_reverse_three _ _ _)

public theorem refinedGenerators_mem (c : Fin 4) (j : Fin 4) :
    refinedGenerators c j ∈ residualCandidate (refinedIndex c) := by
  rw [refinedCandidate_eq_generated]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_range_self j))

public theorem refinedCandidate_eq_comap (c : Fin 4) :
    residualCandidate (refinedIndex c) = (refinedTailNode c).comap projection := by
  apply le_antisymm
  · rw [refinedCandidate_eq_generated]
    apply sup_le
    · rw [← ker_projection]
      intro x hx
      change projection x ∈ refinedTailNode c
      rw [MonoidHom.mem_ker.mp hx]
      exact (refinedTailNode c).one_mem
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j, rfl⟩
      exact refinedGenerators_tailMember c j
  · intro x hx
    let w := refinedTailWord c (projection x)
    let y := Theory.GroupTheory.evalWord (refinedGenerators c) w
    have hy : y ∈ residualCandidate (refinedIndex c) := by
      dsimp [y]
      induction w with
      | nil => exact (residualCandidate (refinedIndex c)).one_mem
      | cons j w ih =>
        exact (residualCandidate (refinedIndex c)).mul_mem (refinedGenerators_mem c j) ih
    have hmap : ∀ w : List (Fin 4),
        projection (Theory.GroupTheory.evalWord (refinedGenerators c) w) =
        Theory.GroupTheory.evalWord (fun j => projection (refinedGenerators c j)) w := by
      intro w
      induction w with
      | nil => exact projection.map_one
      | cons j w ih => exact (projection.map_mul _ _).trans (congrArg _ ih)
    have hxy : projection y = projection x :=
      (hmap w).trans (refinedTailWord_valid c (projection x) hx)
    have htail : y⁻¹ * x ∈ tailSubgroup := by
      rw [← ker_projection, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have h := (residualCandidate (refinedIndex c)).mul_mem hy
      (tailSubgroup_le_residualCandidate _ htail)
    simpa using h

public theorem refinedCandidate_mem (c : Fin 4) (x : SylowModel) :
    x ∈ residualCandidate (refinedIndex c) ↔ refinedTailMember c (projection x) := by
  rw [refinedCandidate_eq_comap]
  rfl

public instance refinedCandidate_decidableMem (c : Fin 4) :
    DecidablePred (fun x => x ∈ residualCandidate (refinedIndex c)) := fun x =>
  decidable_of_iff (refinedTailMember c (projection x)) (refinedCandidate_mem c x).symm

@[expose] public def refinedProjection (c : Fin 4) : residualCandidate (refinedIndex c) →* RefinedQuotient where
  toFun x := refinedCoordinates c (projection x.val)
  map_one' := by
    change refinedCoordinates c (projection 1) = 1
    rw [map_one]
    exact (refinedCoordinates_mul c).1
  map_mul' x y := by
    change refinedCoordinates c (projection (x.val * y.val)) = _
    rw [map_mul]
    exact (refinedCoordinates_mul c).2 _ _
      ((refinedCandidate_mem c x).mp x.property) ((refinedCandidate_mem c y).mp y.property)

@[expose] public def refinedBasisLift (c : Fin 4) (j : Fin 3) : residualCandidate (refinedIndex c) :=
  ⟨refinedGenerators c (refinedBasisPosition c j), refinedGenerators_mem c _⟩

public theorem refinedProjection_basis (c : Fin 4) (j : Fin 3) :
    refinedProjection c (refinedBasisLift c j) = refinedBasis j := refinedCoordinates_basis c j

public theorem refinedProjection_surjective (c : Fin 4) : Function.Surjective (refinedProjection c) := by
  intro v
  refine ⟨Theory.GroupTheory.evalWord (refinedBasisLift c) (refinedWord v), ?_⟩
  have hmap : ∀ w : List (Fin 3),
      refinedProjection c (Theory.GroupTheory.evalWord (refinedBasisLift c) w) =
        Theory.GroupTheory.evalWord refinedBasis w := by
    intro w
    induction w with
    | nil => exact (refinedProjection c).map_one
    | cons j w ih =>
      simp only [Theory.GroupTheory.evalWord, map_mul, refinedProjection_basis, ih]
  exact (hmap _).trans (refinedWord_valid v)
end ReeTwo.SylowModel
