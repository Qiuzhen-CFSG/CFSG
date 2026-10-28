module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Primitive incidence rows distinguish points

An equivariant family of subsets in a transitive action has a row stabilizer
containing the point stabilizer. If the latter is maximal and one row is
nonempty and proper, transitivity makes the row stabilizer proper, so it equals
the point stabilizer. The rows are consequently distinct. This is the local
faithfulness argument in Aschbacher--Smith J.5.6, in reusable action form.
-/

public section
namespace MulAction
open Subgroup
open scoped Pointwise
variable {K X Y:Type*} [Group K] [MulAction K X] [MulAction K Y]
  [IsPretransitive K X] [IsPretransitive K Y]

/-- An equivariant family of nonempty proper rows in a transitive incidence
structure separates points when their stabilizer is maximal. -/
theorem incidence_rows_injective (row:X→Set Y)
    (heq:∀k:K,∀x,row (k•x)=k•row x) (x0:X)
    (hmax:IsCoatom (stabilizer K x0))
    (hne:(row x0).Nonempty) (hproper:row x0≠Set.univ) :
    Function.Injective row := by
  let J:=stabilizer K (row x0)
  have hle:stabilizer K x0≤J := by
    intro k hk
    change k•row x0=row x0
    change k•x0=x0 at hk
    rw [←heq,hk]
  have hJ:J≠⊤ := by
    intro ht
    apply hproper
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨z,hz⟩:=hne
    obtain ⟨k,hk⟩:=exists_smul_eq K z y
    have hs:k∈J := ht.symm ▸ mem_top k
    change k•row x0=row x0 at hs
    have hh:k•z∈k•row x0 := Set.smul_mem_smul_set hz
    rwa [hs,hk] at hh
  have hJX:J=stabilizer K x0 := (hmax.le_iff_eq hJ).mp hle
  intro x y hxy
  obtain ⟨a,rfl⟩:=exists_smul_eq K x0 x
  obtain ⟨b,rfl⟩:=exists_smul_eq K x0 y
  have hab:b⁻¹*a∈J := by
    change (b⁻¹*a)•row x0=row x0
    rw [mul_smul,←heq,hxy,heq,inv_smul_smul]
  have hh:b⁻¹*a∈stabilizer K x0 := hJX ▸ hab
  change (b⁻¹*a)•x0=x0 at hh
  simpa only [mul_smul,smul_inv_smul] using congrArg (fun z=>b•z) hh
end MulAction
