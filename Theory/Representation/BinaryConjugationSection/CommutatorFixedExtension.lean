module
public import Theory.Representation.BinaryConjugationSection.CommutatorImage

/-!
# Commutator images after adjoining a fixed factor

If every element of U is a product from B and C, and the actor's commutators
with C lie in the kernel Z of B/Z, then [A,U] and [A,B] have the same literal
coordinate image. The fixed factor is retained in U throughout the argument.

Source application: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1041.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {H B Z : Subgroup G} {ρ : Representation (ZMod 2) H V}
  (c : BinaryConjugationSection H B Z ρ)

theorem imageSpace_sup_kernel (R : Subgroup G) (hR : R ≤ B) :
    c.imageSpace (R ⊔ Z) = c.imageSpace R := by
  have he : ((R ⊔ Z).subgroupOf B).map c.coordinates =
      (R.subgroupOf B).map c.coordinates := by
    rw [subgroupOf_sup hR c.kernel_le, Subgroup.map_sup, ← c.kernel_eq,
      (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  exact congrArg (fun P : Subgroup (Multiplicative V) =>
    AddSubgroup.toZModSubmodule 2 P.toAddSubgroup') he

/-- A fixed factor contributes only to the original kernel, not to the
commutator image. No equality of the original commutator subgroups is asserted. -/
theorem imageSpace_commutator_of_fixed_extension
    (A U C : Subgroup G) (hAH : A ≤ H) (hBU : B ≤ U)
    (hcover : ∀ u ∈ U, ∃ b ∈ B, ∃ t ∈ C, u = b * t)
    (hfixed : ⁅A,C⁆ ≤ Z) :
    c.imageSpace ⁅A,U⁆ = c.imageSpace ⁅A,B⁆ := by
  have hBZ : B ≤ normalizer (Z : Set G) :=
    (normal_subgroupOf_iff_le_normalizer c.kernel_le).mp c.kernel_normal
  have hR : ⁅A,B⁆ ≤ B :=
    le_normalizer_iff_commutator_le_right.mp (hAH.trans c.normalized)
  have hupper : ⁅A,U⁆ ≤ ⁅A,B⁆ ⊔ Z := by
    apply commutator_le.mpr
    intro a ha u hu
    obtain ⟨b,hb,t,ht,rfl⟩ := hcover u hu
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hm := (⁅A,B⁆ ⊔ Z).mul_mem
      (mem_sup_left (commutator_mem_commutator ha hb))
      (mem_sup_right ((hBZ hb _).mp (hfixed (commutator_mem_commutator ha ht))))
    simpa only [mul_assoc] using hm
  apply le_antisymm
  · exact (c.imageSpace_mono hupper).trans (c.imageSpace_sup_kernel _ hR).le
  · exact c.imageSpace_mono (commutator_mono le_rfl hBU)

end Representation.BinaryConjugationSection
