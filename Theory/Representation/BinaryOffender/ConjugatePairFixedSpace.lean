module
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.GroupAction.SubgroupConjugation
/-!
# Fixed spaces of an exchanged commuting pair

In an irreducible representation, the sum of the fixed spaces of two
commuting subgroups permuted by conjugation is zero or the whole module.
In the second case each subgroup moves only vectors fixed by the other.
This isolates the elementary fixed-space argument used in the exchanged
component cases of Aschbacher--Smith 12.6.33 and 13.8.16.
-/
public section
open Subgroup
namespace Representation.BinaryOffender
private theorem fixed_conjugate_image
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (A : Subgroup D) (g : D) :
    (fixedSpace ρ A).map (ρ g) ≤ fixedSpace ρ (A.conjBy g) := by
  rintro _ ⟨v,hv,rfl⟩ b
  obtain ⟨a,ha,he⟩ := b.property
  have hb : (b : D) = g * a * g⁻¹ := he.symm
  change ρ (b : D) (ρ g v) = ρ g v
  rw [hb]
  simp only [map_mul, Module.End.mul_apply, inv_self_apply]
  exact congrArg (ρ g) (hv ⟨a,ha⟩)

/-- For an irreducible representation with two conjugate components, either
both component fixed spaces vanish, or each component's moved space is
fixed by the other. This uses the literal conjugation orbit, not a module
classification. -/
theorem cross_fixed_or_component_fixed_eq_bot
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) [ρ.IsIrreducible]
    (A B : Subgroup D)
    (hA : ∀ g : D, A.conjBy g = A ∨ A.conjBy g = B)
    (hB : ∀ g : D, B.conjBy g = A ∨ B.conjBy g = B)
    (hc : A ≤ centralizer (B : Set D)) :
    (subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B ∧
      subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A) ∨
    (fixedSpace ρ A = ⊥ ∧ fixedSpace ρ B = ⊥) := by
  let C : Subrepresentation ρ := {
    toSubmodule := fixedSpace ρ A ⊔ fixedSpace ρ B
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      apply Submodule.add_mem
      · have hh := fixed_conjugate_image ρ A g (Submodule.mem_map_of_mem (f := ρ g) ha)
        rcases hA g with he | he
        · exact Submodule.mem_sup_left (he ▸ hh)
        · exact Submodule.mem_sup_right (he ▸ hh)
      · have hh := fixed_conjugate_image ρ B g (Submodule.mem_map_of_mem (f := ρ g) hb)
        rcases hB g with he | he
        · exact Submodule.mem_sup_left (he ▸ hh)
        · exact Submodule.mem_sup_right (he ▸ hh) }
  rcases IsSimpleOrder.eq_bot_or_eq_top C with h | h
  · right
    have hh : fixedSpace ρ A ⊔ fixedSpace ρ B = ⊥ :=
      congrArg Subrepresentation.toSubmodule h
    exact ⟨bot_unique (le_sup_left.trans hh.le),bot_unique (le_sup_right.trans hh.le)⟩
  · left
    have hh : fixedSpace ρ A ⊔ fixedSpace ρ B = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    have hf (X Y : Subgroup D) (hXY : X ≤ centralizer (Y : Set D))
        (hs : fixedSpace ρ X ⊔ fixedSpace ρ Y = ⊤) :
        subspaceCommutator ρ ⊤ X ≤ fixedSpace ρ Y := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x,hx,v,_,rfl⟩
      obtain ⟨u,hu,w,hw,he⟩ := Submodule.mem_sup.mp (hs.symm ▸ (Submodule.mem_top (x := v)))
      have hxu : ρ x u = u := hu ⟨x,hx⟩
      rw [← he,map_add,hxu]
      have heq : u + ρ x w - (u+w) = ρ x w - w := by abel
      rw [heq]
      apply (fixedSpace ρ Y).sub_mem _ hw
      intro y
      change ρ y (ρ x w) = ρ x w
      rw [← Module.End.mul_apply, ← map_mul, (hXY hx y y.property),map_mul,
        Module.End.mul_apply]
      exact congrArg (ρ x) (hw y)
    exact ⟨hf A B hc hh,hf B A (le_centralizer_iff.mp hc) (by rwa [sup_comm])⟩

end Representation.BinaryOffender
