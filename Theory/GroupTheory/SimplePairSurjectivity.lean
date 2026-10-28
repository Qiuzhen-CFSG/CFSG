module
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Separating simple quotient maps

A nontrivial kernel in a separating pair of surjective homomorphisms maps
onto the simple second factor. Correcting a preimage by that kernel proves
surjectivity onto the direct product. This is the elementary subdirect-product
argument used for Aschbacher–Smith G.11.2(12).
-/
public section
open Subgroup
namespace Theory.GroupTheory
/-- Two separating simple quotient maps, one with a nontrivial kernel,
identify their common source with the full direct product. -/
theorem surjective_simple_pair {H A B : Type*} [Group H] [Group A] [Group B]
    [IsSimpleGroup B] (f : H →* A) (g : H →* B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hinj : Function.Injective (f.prod g)) (hne : f.ker ≠ ⊥) :
    Function.Surjective (f.prod g) := by
  have hn : (f.ker.map g).Normal := Subgroup.Normal.map inferInstance g hg
  have ht : f.ker.map g = ⊤ := by
    apply hn.eq_bot_or_eq_top.resolve_left
    intro hb
    apply hne
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply hinj
    apply Prod.ext
    · exact (MonoidHom.mem_ker.mp ha).trans (map_one f).symm
    · exact (mem_bot.mp (hb ▸ mem_map_of_mem g ha)).trans (map_one g).symm
  rintro ⟨a,b⟩
  obtain ⟨x,hx⟩ := hf a
  obtain ⟨y,hy,hyb⟩ := (show (g x)⁻¹*b ∈ f.ker.map g from ht ▸ mem_top _)
  refine ⟨x*y,Prod.ext ?_ ?_⟩
  · change f (x*y) = a
    rw [map_mul,MonoidHom.mem_ker.mp hy,mul_one,hx]
  · change g (x*y) = b
    rw [map_mul,hyb,mul_inv_cancel_left]
end Theory.GroupTheory

