module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.FixedMasks
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport.Coordinates

/-!
# Literal quotient lifts and kernel centralizers

The source rows are lifted through the original max1 quotient. The native
kernel action identifies the fixed-mask certificates with the actual kernel
centralizer of every subgroup having the selected image. No assertion about
an entire ambient centralizer is built into the row hypothesis.
Source: Kleidman--Wilson (1988), Propositions 2.3.4--2.3.5.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality Cardinality.QuotientCount Cardinality.QuotientCount.Image
open SylowCore SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

local notation "L" => SylowCore.Local
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four
local notation "e" => maskEquiv matrixA_mul_self matrixB_pow_four
local notation "act" => action matrixA_mul_self matrixB_pow_four

private def starAction : StarGroup →* Equiv.Perm E :=
  (π).liftOfSurjective (starProjection_surjective _ _)
    ⟨act, by rw [starProjection_ker, action_ker_eq_localKernel]⟩

private theorem starAction_projection (g : L) : starAction (π g) = act g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem starAction_fixed_iff (g : StarGroup) (m : Fin 2048) :
    starAction g (e m) = e m ↔ starMask g m.val = m.val := by
  obtain ⟨x,rfl⟩ := starProjection_surjective matrixA_mul_self matrixB_pow_four g
  rw [starAction_projection, ← maskEquiv_starMask]
  exact (e).injective.eq_iff.trans Fin.ext_iff

private def fixer (m : Fin 2048) : Subgroup StarGroup :=
  (MulAction.stabilizer (Equiv.Perm E) (e m)).comap starAction

private theorem mem_fixer (g : StarGroup) (m : Fin 2048) :
    g ∈ fixer m ↔ starMask g m.val = m.val := starAction_fixed_iff g m

/-- Fixedness on generators is equivalent to fixedness on their actual closure. -/
theorem starMask_closure_fixed_iff {ι : Type*} (v : ι → StarGroup) (m : Fin 2048) :
    (∀ g ∈ closure (Set.range v), starMask g m.val = m.val) ↔
      ∀ i, starMask (v i) m.val = m.val := by
  simp_rw [← mem_fixer]
  change closure (Set.range v) ≤ fixer m ↔ _
  rw [closure_le]
  exact Set.range_subset_iff

/-- Testing the displayed generators suffices for the whole quotient row. -/
theorem fixedTest_iff_row (r : Fin 4) (m : Fin 2048) :
    fixedTest r m ↔ ∀ g ∈ rowImage r, starMask g m.val = m.val := by
  simp_rw [← mem_fixer]
  change _ ↔ rowImage r ≤ fixer m
  rw [rowImage, closure_le, Set.range_subset_iff]
  change fixedTest r m ↔ ∀ j, rowGenerator r j ∈ fixer m
  simp only [mem_fixer, rowGenerator_mask, fixedTest]

/-- The kernel centralizer is the fixed space of the literal quotient image. -/
theorem mask_mem_centralizer_iff_image (A : Subgroup L) (m : Fin 2048) :
    (e m : L) ∈ centralizer (A : Set L) ↔
      ∀ g ∈ A.map π, starMask g m.val = m.val := by
  constructor
  · intro h g hg
    obtain ⟨x,hx,rfl⟩ := hg
    apply (starAction_fixed_iff (π x) m).mp
    rw [starAction_projection]
    apply Subtype.ext
    change x * (e m : L) * x⁻¹ = (e m : L)
    rw [h x hx, mul_inv_cancel_right]
  · intro h x hx
    have hf := (starAction_fixed_iff (π x) m).mpr (h _ (mem_map_of_mem _ hx))
    rw [starAction_projection] at hf
    have hv := congrArg (fun v : E => (v : L)) hf
    exact mul_inv_eq_iff_eq_mul.mp hv

/-- Exact native kernel fixed-space equation, for the literal local quotient. -/
theorem mask_mem_centralizer_iff (A : Subgroup L) (r : Fin 4)
    (hrow : A.map π = rowImage r) (m : Fin 2048) :
    (e m : L) ∈ centralizer (A : Set L) ↔ fixedTest r m := by
  rw [mask_mem_centralizer_iff_image, hrow, ← fixedTest_iff_row]

/-- A bijection onto the actual kernel centralizer, not just an upper bound. -/
def fixedMasksEquiv (A : Subgroup L) (r : Fin 4) (hrow : A.map π = rowImage r) :
    fixedMasks r ≃ (centralizer (A : Set L)).subgroupOf E where
  toFun m := ⟨e m.val, (mask_mem_centralizer_iff A r hrow m.val).mpr m.property⟩
  invFun x := ⟨(e).symm x.val, (mask_mem_centralizer_iff A r hrow ((e).symm x.val)).mp
    (by simpa only [(e).apply_symm_apply] using (show (x.val : L) ∈ centralizer (A : Set L) from x.property))⟩
  left_inv m := Subtype.ext ((e).symm_apply_apply m.val)
  right_inv x := Subtype.ext ((e).apply_symm_apply x.val)

/-- The two full rows have four-dimensional kernel fixed spaces; both primed
rows have five-dimensional kernel fixed spaces before the marked-pair condition. -/
theorem kernel_centralizer_card (A : Subgroup L) (r : Fin 4)
    (hrow : A.map π = rowImage r) :
    Nat.card ((centralizer (A : Set L)).subgroupOf E) = if r.val < 2 then 16 else 32 := by
  rw [← Nat.card_congr (fixedMasksEquiv A r hrow)]
  fin_cases r
  · exact fixedMasks0_card
  · exact fixedMasks1_card
  · exact fixedMasks2_card
  · exact fixedMasks3_card

end Janko4.LocalStructure.ElementaryEightGeometry
