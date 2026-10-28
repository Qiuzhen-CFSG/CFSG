module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Data

/-!
# Generating the elementary initial segments by conjugates

The eight products of the three elementary generators form the candidate
largest elementary subgroup. For a nonidentity product, explicit products
of conjugates recover the generators of its highest initial segment. Thus
any subgroup invariant under the specified HS two-subgroup and containing
that product contains the whole corresponding initial segment.

Source: the concrete ATLAS subgroup for GLS volume 3, Table 5.3m, printed p.274.
The identities are reproduced by `source/generate.py` and checked in Lean.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
open Subgroup Theory.GroupTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option Elab.async false

/-- The elements of the largest elementary candidate in binary order. -/
def small : Fin 8 → Carrier := ![1, e0, e1, e0 * e1, e2, e0 * e2, e1 * e2, e0 * e1 * e2]

def actor : Fin 4 → Carrier := ![1, s0, s1, s0 * s1]

def seedWord : Fin 8 → Fin 3 → List (Fin 4) := ![![[], [], []], ![[0], [], []], ![[0, 1], [0], []], ![[0, 1], [1], []], ![[2, 3], [0, 3], [0]], ![[2, 3], [0, 3], [0, 2, 3]], ![[0, 1], [1, 2], [0, 1, 2]], ![[0, 1], [1, 2], [2]]]

private theorem seed_formula_point : ∀ (j : Fin 8) (k : Fin 3),
    ∀ x : Fin 100, 2 ^ k.val ≤ j.val →
    ((evalWord (fun a => actor a * small j * (actor a)⁻¹) (seedWord j k) : Carrier) :
      Equiv.Perm (Fin 100)) x = (elementaryGenerator k : Equiv.Perm (Fin 100)) x := by
  apply allFin₃
  decide +kernel

theorem seed_formula (j : Fin 8) (k : Fin 3) (hk : 2 ^ k.val ≤ j.val) :
    evalWord (fun a => actor a * small j * (actor a)⁻¹) (seedWord j k) =
      elementaryGenerator k := by
  exact Subtype.ext (Equiv.ext (fun x => seed_formula_point j k x hk))

theorem actor_mem (a : Fin 4) : actor a ∈ subgroup := by
  have h0 : s0 ∈ subgroup := subset_closure ⟨0, rfl⟩
  have h1 : s1 ∈ subgroup := subset_closure ⟨1, rfl⟩
  fin_cases a
  · exact subgroup.one_mem
  · exact h0
  · exact h1
  · exact subgroup.mul_mem h0 h1

theorem initial_le_of_small_mem (H : Subgroup Carrier)
    (hn : ∀ x ∈ H, ∀ g ∈ subgroup, g * x * g⁻¹ ∈ H)
    {j : Fin 8} (hj : small j ∈ H) (k : Fin 3) (hk : 2 ^ k.val ≤ j.val) :
    elementaryGenerator k ∈ H := by
  rw [← seed_formula j k hk]
  have hmem : ∀ a, actor a * small j * (actor a)⁻¹ ∈ H :=
    fun a => hn _ hj _ (actor_mem a)
  induction seedWord j k with
  | nil => exact H.one_mem
  | cons a w ih => exact H.mul_mem (hmem a) ih

theorem small_mem_elementary (j : Fin 8) (i : Fin 3)
    (h : j.val < 2 ^ (i.val + 1)) : small j ∈ elementary i := by
  have h0 : ∀ i : Fin 3, e0 ∈ elementary i :=
    fun i => subset_closure ⟨0, by simp, rfl⟩
  have h1 : ∀ i : Fin 3, 1 ≤ i → e1 ∈ elementary i :=
    fun i hi => subset_closure ⟨1, hi, rfl⟩
  have h2 : e2 ∈ elementary 2 := subset_closure ⟨2, by decide, rfl⟩
  fin_cases i <;> fin_cases j <;> norm_num at h
  all_goals first
    | exact (elementary _).one_mem
    | exact h0 _
    | exact h1 _ (by decide)
    | exact h2
    | exact (elementary _).mul_mem (h0 _) (h1 _ (by decide))
    | exact (elementary _).mul_mem (h0 _) h2
    | exact (elementary _).mul_mem (h1 _ (by decide)) h2
    | exact (elementary _).mul_mem ((elementary _).mul_mem (h0 _) (h1 _ (by decide))) h2

end Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
