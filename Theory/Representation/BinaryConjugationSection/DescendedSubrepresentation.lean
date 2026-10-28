module
public import Theory.Representation.BinaryConjugationSection.CoordinateEmbedding

/-!
# Original support coordinates under a descended actor

Nested binary sections with the same kernel give an injective coordinate map.
If their actor homomorphisms commute, surjectivity on the smaller actor makes
this map an intertwiner for the descended action. Its range is exactly the
image of the original subgroup, without a complement or splitting assumption.

Source application: Aschbacher--Smith, 14.6.22--24, pp.1038--1041.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G D J E V : Type*} [Group G] [Group D] [Group J]
  [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup V] [Module (ZMod 2) V]
  {H K U A Z : Subgroup G} {ρ : Representation (ZMod 2) D E}
  {σ : Representation (ZMod 2) J V}

/-- Realize a literal section as a subrepresentation of the same whole quotient. -/
theorem exists_descended_subrepresentation
    (π : H →* D) (κ : J →* D) (f : K →* J) (hf : Function.Surjective f)
    (c : BinaryConjugationSection H U Z (ρ.comp π))
    (d : BinaryConjugationSection K A Z (σ.comp f))
    (hKH : K ≤ H) (hAU : A ≤ U)
    (hπ : ∀ k : K, π (inclusion hKH k) = κ (f k)) :
    ∃ R : Subrepresentation (ρ.comp κ),
      R.toSubmodule = c.imageSpace A ∧
      ∃ e : V ≃ₗ[ZMod 2] R.toSubmodule,
        (∀ j v, e (σ j v) = R.toRepresentation j (e v)) ∧
        ∀ a : A, (e (d.coordinates a).toAdd : E) =
          (c.coordinates (inclusion hAU a)).toAdd := by
  obtain ⟨emb,hi,hcoord,hact,hrange⟩ := c.exists_coordinate_embedding d hKH hAU
  have hact' (j : J) (v : V) : (ρ.comp κ) j (emb v) = emb (σ j v) := by
    obtain ⟨k,rfl⟩ := hf j
    have hh := hact k v
    change ρ (π (inclusion hKH k)) (emb v) = emb (σ (f k) v) at hh
    rwa [hπ] at hh
  let R : Subrepresentation (ρ.comp κ) := {
    toSubmodule := emb.range
    apply_mem_toSubmodule j := by
      rintro _ ⟨v,rfl⟩
      exact ⟨σ j v,(hact' j v).symm⟩ }
  let e : V ≃ₗ[ZMod 2] R.toSubmodule := LinearEquiv.ofInjective emb hi
  refine ⟨R,hrange,e,?_,hcoord⟩
  intro j v
  exact Subtype.ext (hact' j v).symm
end Representation.BinaryConjugationSection
