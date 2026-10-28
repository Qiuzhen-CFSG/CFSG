module
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport

/-!
# Centralizing actors on a whole Irr⁺ module

The displacement image of an actor centralizing the group is invariant.
If that image is proper, Irr⁺ makes it fixed. The displacement then kills
the whole group commutator, which generates the module. Faithfulness
excludes this for a nonidentity actor, so its displacement is surjective.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.833, applied to the
central cubic on the original section U_H/V₁.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]

/-- Every nonidentity centralizing actor displaces a faithful whole Irr⁺
module onto itself. This retains the actual actor, without absolute irreducibility. -/
theorem IsIrrPlus.centralizing_displacement_eq_top
    (σ : Representation (ZMod 2) J W) (hf : Function.Injective σ)
    {B : Subgroup J} (hi : IsIrrPlus σ B ⊤)
    (x : J) (hx : x ∈ centralizer (B : Set J)) (hne : x ≠ 1) :
    LinearMap.range (σ x - LinearMap.id) = ⊤ := by
  let f := σ x - LinearMap.id
  have hcomm (b : B) (w : W) : σ b (f w) = f (σ b w) := by
    change σ b (σ x w - w) = σ x (σ b w) - σ b w
    rw [map_sub]
    congr 1
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    rw [hx b b.property]
  have hinv : B ≤ subspaceStabilizer σ f.range := by
    apply le_subspaceStabilizer
    rintro b hb w ⟨v,rfl⟩
    exact ⟨σ b v,(hcomm ⟨b,hb⟩ v).symm⟩
  rcases hi.eq_or_le_fixedSpace σ hinv le_top with he | hc
  · exact he
  · have hkill : subspaceCommutator σ ⊤ B ≤ f.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨b,hb,w,_,rfl⟩
      change f (σ b w - w) = 0
      rw [map_sub,←hcomm ⟨b,hb⟩ w]
      exact sub_eq_zero.mpr (hc (show f w ∈ f.range from ⟨w,rfl⟩) ⟨b,hb⟩)
    rw [hi.choose_spec.1] at hkill
    have he : σ x = σ 1 := by
      ext w
      have hh := hkill (Submodule.mem_top (x := w))
      change σ x w - w = 0 at hh
      simpa only [map_one,Module.End.one_apply] using sub_eq_zero.mp hh
    exact (hne (hf he)).elim

end Representation.BinaryOffender
