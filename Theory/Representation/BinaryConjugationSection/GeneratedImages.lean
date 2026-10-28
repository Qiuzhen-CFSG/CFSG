module

public import Theory.Representation.BinaryConjugationSection.InvariantImages

/-!
# Images invariant under generating subgroups

If two ambient subgroup images coincide, and each image is preserved by
one of two generating actor groups, their common image is invariant under
the whole group. In an irreducible section a nonzero such image is the
whole module. This uses the literal conjugation-section coordinates.

Source application: the tensor plane and its L₁-span in Aschbacher–Smith,
13.8.30, printed p.964.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H A N : Subgroup G} {ρ : Representation (ZMod 2) H W}
  (q : BinaryConjugationSection H A N ρ)

/-- Generation makes equal images under the two invariant subgroups invariant under H. -/
theorem image_eq_top_of_generators [IsIrreducible ρ]
    (B S : Subgroup G) (J K : Subgroup H) (hgen : J ⊔ K = ⊤)
    (hJ : ∀ j : J, ((j : H) : G) ∈ normalizer S)
    (hK : ∀ k : K, ((k : H) : G) ∈ normalizer B)
    (he : q.imageSpace S = q.imageSpace B) (hn : q.imageSpace B ≠ ⊥) :
    q.imageSpace B = ⊤ := by
  let P := q.imageSpace B
  let T : Subgroup H := {
    carrier := {h | ∀ w, ρ h w ∈ P ↔ w ∈ P}
    one_mem' := by intro w; simp
    mul_mem' := by
      intro a b ha hb w
      simpa only [map_mul, Module.End.mul_apply] using (ha (ρ b w)).trans (hb w)
    inv_mem' := by
      intro a ha w
      have hh := (ha (ρ a⁻¹ w)).symm
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] using hh }
  have hmem (a : H) (hf : ∀ w ∈ P, ρ a w ∈ P)
      (hb : ∀ w ∈ P, ρ a⁻¹ w ∈ P) : a ∈ T := by
    intro w
    constructor
    · intro hw
      have hh := hb _ hw
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply] using hh
    · exact hf w
  have hJT : J ≤ T := by
    intro a ha
    apply hmem
    · intro w hw
      change w ∈ q.imageSpace B at hw
      change _ ∈ q.imageSpace B
      rw [← he] at hw ⊢
      exact q.imageSpace_apply_mem S a (hJ ⟨a,ha⟩) w hw
    · intro w hw
      change w ∈ q.imageSpace B at hw
      change _ ∈ q.imageSpace B
      rw [← he] at hw ⊢
      exact q.imageSpace_apply_mem S a⁻¹ (hJ ⟨a⁻¹,J.inv_mem ha⟩) w hw
  have hKT : K ≤ T := by
    intro a ha
    exact hmem a (q.imageSpace_apply_mem B a (hK ⟨a,ha⟩))
      (q.imageSpace_apply_mem B a⁻¹ (hK ⟨a⁻¹,K.inv_mem ha⟩))
  have htop : T = ⊤ := top_unique (hgen ▸ sup_le hJT hKT)
  let R : Subrepresentation ρ := {
    toSubmodule := P
    apply_mem_toSubmodule a := fun w hw =>
      (show a ∈ T from htop ▸ mem_top a) w |>.mpr hw }
  rcases eq_bot_or_eq_top R with hb | ht
  · exact (hn (congrArg Subrepresentation.toSubmodule hb)).elim
  · exact congrArg Subrepresentation.toSubmodule ht
end Representation.BinaryConjugationSection

