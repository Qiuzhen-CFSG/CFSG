module
public import Theory.Representation.BinaryConjugationSection.Coinvariants
public import Theory.Representation.FirstCohomologyDuality
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Module.ZMod

/-!
# A central module cover from original conjugation coordinates

A fully moved elementary abelian subgroup with fixed coordinate kernel is a
central cover of its marked quotient representation. The linear covering map
is exactly the original coordinate homomorphism, and full movement becomes
coinvariant generation. This supplies the literal-cover input for the natural
A₅ kernel bound in Aschbacher–Smith 10.1.1 and 10.2.12, pp.741 and754.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Representation.BinaryConjugationSection
variable {G J V : Type*} [Group G] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V]
  {H W Z : Subgroup G} [IsElementaryAbelian 2 W]
  (ρ : Representation (ZMod 2) J V) (q : H →* J) (hq : Function.Surjective q)
  (c : BinaryConjugationSection H W Z (ρ.comp q))
  (σ : Representation (ZMod 2) J (Additive W))
  (hσ : ∀ (l : H) (w : Additive W),
    ((σ (q l) w).toMul : G) = l * w.toMul * (l : G)⁻¹)

include hq hσ in
/-- Full group commutator generation gives a central cover with the same coordinates. -/
theorem exists_cover_of_fully_moved
    (hfixed : Z ≤ centralizer (H : Set G)) (hmoved : ⁅W,H⁆ = W) :
    ∃ p : σ.IntertwiningMap ρ, OneCohomology.IsCover p ∧
      ∀ w : Additive W, p w = (c.coordinates w.toMul).toAdd := by
  let p : Additive W →+ V := {
    toFun w := (c.coordinates w.toMul).toAdd
    map_zero' := c.coordinates.map_one
    map_add' _ _ := c.coordinates.map_mul _ _ }
  let f : σ.IntertwiningMap ρ := {
    toLinearMap := p.toZModLinearMap 2
    isIntertwining' := by
      intro a
      apply LinearMap.ext
      intro w
      obtain ⟨l,rfl⟩ := hq a
      have hs : (σ (q l) w).toMul =
          (⟨(l : G)*w.toMul*(l : G)⁻¹,
            (mem_normalizer_iff.mp (c.normalized l.property) w.toMul).mp w.toMul.property⟩ : W) :=
        Subtype.ext (hσ l w)
      change (c.coordinates (σ (q l) w).toMul).toAdd = ρ (q l) (c.coordinates w.toMul).toAdd
      rw [hs]
      exact c.equivariant l w.toMul }
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨w,hw⟩ := c.onto (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul w,congrArg Multiplicative.toAdd hw⟩
  have hk : f.toLinearMap.ker ≤ OneCohomology.fixed σ := by
    intro w hw a
    have hz : (w.toMul : G) ∈ Z := (c.coordinates_eq_one_iff w.toMul).mp hw
    obtain ⟨l,rfl⟩ := hq a
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ]
    have hh : (l : G) * (w.toMul : G) = (w.toMul : G) * (l : G) := hfixed hz l l.property
    rw [hh,mul_inv_cancel_right]
  let d : BinaryConjugationSection H W ⊥ (σ.comp q) := {
    section_le := c.section_le
    kernel_le := bot_le
    normalized := c.normalized
    coordinates := {
      toFun w := Multiplicative.ofAdd (Additive.ofMul w)
      map_one' := rfl
      map_mul' _ _ := rfl }
    onto := fun w => ⟨w.toAdd.toMul,rfl⟩
    kernel_eq := by
      ext w
      change w = 1 ↔ (w : G) = 1
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    equivariant := by
      intro l w
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (hσ l (Additive.ofMul w)).symm }
  have hm : Coinvariants.ker σ = ⊤ :=
    d.coinvariants_eq_top_of_group_generation H le_rfl σ q (fun _ _ => rfl) (by
      rw [sup_bot_eq,commutator_comm,hmoved])
  exact ⟨f,⟨hf,hk,hm⟩,fun _ => rfl⟩
end Representation.BinaryConjugationSection
