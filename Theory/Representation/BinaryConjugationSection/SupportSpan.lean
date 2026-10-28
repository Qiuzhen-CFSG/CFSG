module
public import Theory.Representation.BinaryConjugationSection.FixedMoving
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# Lifting a moving-plus-fixed span through the original kernel

A spanning sum in U/Z lifts to a subgroup join with the literal commutator
preimage. The discrepancy between coordinate lifts lies in Z, which is
retained in the moving subgroup. No split covering or direct-sum assumption
is needed.

Source application: Aschbacher--Smith, 14.6.23(3), printed p.1038.
-/

public section
open Subgroup Representation.OneCohomology
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G E : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H E}

/-- Lift the quotient span without choosing a complement to the central kernel. -/
theorem le_sup_fixed_preimage_of_spanning_image
    (c : BinaryConjugationSection H U Z ρ) (A : Subgroup G)
    (hZA : Z ≤ A) (hUZ : U ≤ normalizer (Z : Set G))
    (hspan : c.imageSpace A ⊔ fixed ρ = ⊤) :
    U ≤ A ⊔ commutatorPreimage U H Z := by
  intro v hv
  have hvspan : (c.coordinates ⟨v,hv⟩).toAdd ∈ c.imageSpace A ⊔ fixed ρ := by
    rw [hspan]; trivial
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hvspan
  obtain ⟨a,ha,hax⟩ := (c.mem_imageSpace_iff A x).mp hx
  obtain ⟨b,hb⟩ := c.onto (Multiplicative.ofAdd y)
  have hbC : (b:G) ∈ commutatorPreimage U H Z := by
    apply (mem_commutatorPreimage_iff U H Z hUZ b).mpr
    refine ⟨b.property,?_⟩
    intro k hk
    apply (c.fixed_coordinate_iff_commutator_mem ⟨k,hk⟩ b).mp
    rw [hb]
    exact hy ⟨k,hk⟩
  have he : c.coordinates (a*b) = c.coordinates ⟨v,hv⟩ := by
    rw [map_mul]
    apply Multiplicative.toAdd.injective
    change (c.coordinates a).toAdd + (c.coordinates b).toAdd = _
    rw [hax,hb]
    exact hxy
  have hz : v*((a:G)*(b:G))⁻¹ ∈ Z := by
    apply (c.coordinates_eq_one_iff (⟨v,hv⟩*(a*b)⁻¹)).mp
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hab : (a:G)*(b:G) ∈ A ⊔ commutatorPreimage U H Z := mul_mem_sup ha hbC
  have hz' : v*((a:G)*(b:G))⁻¹ ∈ A ⊔ commutatorPreimage U H Z :=
    (show A ≤ A ⊔ commutatorPreimage U H Z from le_sup_left) (hZA hz)
  simpa only [inv_mul_cancel_right] using (A ⊔ commutatorPreimage U H Z).mul_mem hz' hab
end Representation.BinaryConjugationSection
