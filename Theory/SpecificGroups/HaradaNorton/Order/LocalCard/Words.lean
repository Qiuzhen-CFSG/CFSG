module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard.Certificate

/-!
# Concrete candidate Suzuki generators for the HN word subgroup

These ten positive words are obtained from the degree-twelve permutations
`(1,2)(3,4)(5,6)(7,8)(9,10)(11,12)` and
`(1,7,3,2)(4,6)(5,11)(10,12)`. GAP rewrites the Suzuki generators
`(1,2)(i,i+1)`, for `i = 2,...,11`, in that pair. The words are evaluated
here in the original HN subgroup, without assuming a homomorphism from the
permutation group. The companion recovery words propose expressions for
`a` and `localB` in the ten generators.

`source/CheckWitness.py` checks the saved candidate relations numerically.
Those computations are only witness discovery;
this module proves membership and the implication from recovery identities
to generation, and makes no claim that the matrix identities are certified.
The original matrix attribution is in `../../MatrixSources.md`.
-/

namespace HaradaNorton.OrderCertificate

/-- The original two generators viewed inside the actual subgroup. -/
@[expose] public def localPair : Fin 2 → localSubgroup :=
  ![⟨a, a_mem_localSubgroup⟩, ⟨localB, localB_mem_localSubgroup⟩]

/-- Positive words, with letters numbered zero and one. -/
@[expose] public def localSuzukiWords : Fin 10 → List (Fin 2 × Nat) :=
  ![[(1, 2), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 2), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1)],
    [(1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 2)],
    [(1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2)],
    [(1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3)],
    [(0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1)],
    [(1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1)],
    [(1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1)],
    [(0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1)],
    [(0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2)],
    [(1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 1), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (1, 3), (0, 1), (1, 2), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1), (1, 3), (0, 1)]]

/-- Evaluation uses only positive powers, so membership needs no matrix facts. -/
@[expose] public def evalLocalPairWord (w : List (Fin 2 × Nat)) : localSubgroup :=
  (w.map fun s => localPair s.1 ^ s.2).prod

/-- The proposed ten elements in the concrete word subgroup. -/
@[expose] public def localSuzukiGen (i : Fin 10) : localSubgroup :=
  evalLocalPairWord (localSuzukiWords i)

/-- Short candidate expressions recovering the two original generators. -/
@[expose] public def localSuzukiRecoveryWords : Fin 2 → List (Fin 10 × Nat) :=
  ![[(1, 1), (3, 1), (5, 1), (7, 1), (9, 1)],
    [(0, 1), (1, 1), (3, 1), (2, 1), (1, 1), (4, 1), (3, 1), (2, 1), (1, 1), (5, 1), (6, 1), (8, 1), (7, 1), (6, 1), (5, 1), (4, 1), (3, 1), (9, 1), (8, 1)]]

/-- Evaluate a positive word in the ten concrete candidates. -/
@[expose] public def evalLocalSuzukiWord (w : List (Fin 10 × Nat)) : localSubgroup :=
  (w.map fun s => localSuzukiGen s.1 ^ s.2).prod

private theorem evalLocalSuzukiWord_mem (w : List (Fin 10 × Nat)) :
    evalLocalSuzukiWord w ∈ Subgroup.closure (Set.range localSuzukiGen) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
  exact (Subgroup.closure (Set.range localSuzukiGen)).pow_mem
    (Subgroup.subset_closure ⟨s.1, rfl⟩) s.2

/-- Only the two recovery equalities are needed to certify generation.
Their numerical discovery is not used in this proof. -/
public theorem localSuzukiGen_generates_of_recovery
    (h : ∀ i : Fin 2,
      evalLocalSuzukiWord (localSuzukiRecoveryWords i) = localPair i) :
    Subgroup.closure (Set.range localSuzukiGen) = ⊤ := by
  let S := Subgroup.closure (Set.range localSuzukiGen)
  have hpair (i : Fin 2) : localPair i ∈ S :=
    h i ▸ evalLocalSuzukiWord_mem (localSuzukiRecoveryWords i)
  have hle : localSubgroup ≤ S.map localSubgroup.subtype := by
    change Subgroup.closure {a, localB} ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨localPair 0, hpair 0, rfl⟩
    · exact ⟨localPair 1, hpair 1, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  exact (Subtype.ext he : y = x) ▸ hy

end HaradaNorton.OrderCertificate
