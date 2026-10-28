module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Presentation

/-!
# A literal subgroup chain in the reduced presentation

The first two generators of the local subgroup are the reduced presentation's
second and third generators; the third is its sixth generator. The first four
defining relators prove that the first two generate a finite dihedral quotient
of order at most six. A cover of the local subgroup by 3,360 cosets of this
small subgroup would consequently give the local bound 20,160.

The anticipated indices are discovery data, not assumptions here. No
permutation-image cardinality is used. Source: the exact 597 words in
`../source/presentation.json`, through `Reduced.Presentation`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound
open Subgroup.CosetWordCertificate

/-- Zero-based indices of the three literal generators. -/
def localIndex : Fin 3 → Fin 10 := ![1, 2, 5]

def localGenerator (i : Fin 3) : Carrier := generator (localIndex i)

def localSubgroup : Subgroup Carrier := Subgroup.closure (Set.range localGenerator)

theorem localGenerator_mem (i : Fin 3) : localGenerator i ∈ localSubgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

def subgroupGenerator (i : Fin 3) : localSubgroup :=
  ⟨localGenerator i, localGenerator_mem i⟩

theorem subgroupGenerator_generates :
    Subgroup.closure (Set.range subgroupGenerator) = ⊤ := by
  apply Subgroup.map_injective localSubgroup.subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp]
  change Subgroup.closure (Set.range localGenerator) =
    Subgroup.map localSubgroup.subtype ⊤
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

theorem second_square : generator 1 ^ 2 = 1 := by
  have hw : relatorWord 0 = [(1, true), (1, true)] := by decide +kernel
  have h := relator_valid 0
  rw [hw] at h
  simpa [eval_cons, pow_two] using h

theorem third_square : generator 2 ^ 2 = 1 := by
  have hw : relatorWord 1 = [(2, true), (2, true)] := by decide +kernel
  have h := relator_valid 1
  rw [hw] at h
  simpa [eval_cons, pow_two] using h

theorem second_third_cube : (generator 1 * generator 2) ^ 3 = 1 := by
  have hw : relatorWord 3 =
      [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)] :=
    by decide +kernel
  have h := relator_valid 3
  rw [hw] at h
  simpa [eval_cons, pow_succ, mul_assoc] using h

/-- This is a subgroup of `localSubgroup`, not an ambient normal closure. -/
def smallSubgroup : Subgroup localSubgroup :=
  Subgroup.closure ({subgroupGenerator 1, subgroupGenerator 0} : Set localSubgroup)

theorem smallSubgroup_finite_card :
    Finite smallSubgroup ∧ Nat.card smallSubgroup ≤ 6 := by
  apply Subgroup.closure_pair_finite_card_le_of_involutions (by decide : 0 < 3)
  · apply Subtype.ext
    exact third_square
  · apply Subtype.ext
    exact second_square
  · apply Subtype.ext
    exact second_third_cube

/-- An actual coset cover, if constructed, gives the required local bound. -/
theorem local_finite_card_of_cover
    (C : Subgroup.GeneratorCosetCover smallSubgroup subgroupGenerator (Fin 3360)) :
    Finite localSubgroup ∧ Nat.card localSubgroup ≤ 20160 := by
  let : Finite smallSubgroup := smallSubgroup_finite_card.1
  obtain ⟨hf, hc⟩ := C.finite_card_le subgroupGenerator_generates
  refine ⟨hf, hc.trans ?_⟩
  simpa using Nat.mul_le_mul_right 3360 smallSubgroup_finite_card.2

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound
