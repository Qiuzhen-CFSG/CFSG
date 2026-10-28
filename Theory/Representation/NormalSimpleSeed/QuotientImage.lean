module
public import Theory.Representation.NormalSimpleSeed

/-!
# Fixed vectors when the seed actor has normal image

Suppose a simple, nontrivial seed generates a binary representation under
its whole actor group. The seed actor need only have normal image under a
homomorphism whose kernel acts trivially on the representation. Pulling the
normal image back gives an actual normal subgroup with the same operators
as the seed actor. Clifford semisimplicity then gives no fixed vectors.

This keeps normality of the image distinct from normality of its chosen
lift. The application is the last central-quotient argument in
Aschbacher--Smith, 14.3.25, printed p.1001.
-/

public section
open Subgroup Representation.BinaryOffender
namespace Representation

/-- A nontrivial simple generating seed has no fixed vectors when its actor's
image is normal and the kernel of that image acts trivially. -/
theorem fixed_eq_zero_of_normal_image_simple_seed
    {A B J X Y : Type*} [Group A] [Group B] [Group J]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) A X) (σ : Representation (ZMod 2) J Y)
    (q : A →* B) (k : J →* A) (hker : q.ker ≤ ρ.ker)
    (hn : (q.comp k).range.Normal)
    (ι : Y →ₗ[ZMod 2] X) (hi : Function.Injective ι)
    (he : ∀ j y, ι (σ j y) = ρ (k j) (ι y))
    (hs : IsIrreducible σ) (hm : ∃ j y, σ j y ≠ y)
    (hgen : ∀ R : Subrepresentation ρ, LinearMap.range ι ≤ R.toSubmodule → R = ⊤) :
    ∀ x, (∀ j, ρ (k j) x = x) → x = 0 := by
  let := hn
  let N := (q.comp k).range.comap q
  let : N.Normal := inferInstanceAs ((q.comp k).range.comap q).Normal
  let τ := ρ.comp N.subtype
  have same (n : N) : ∃ j, ρ n = ρ (k j) := by
    obtain ⟨j,hj⟩ := n.property
    have hx : (n:A) * (k j)⁻¹ ∈ q.ker := by
      change q ((n:A) * (k j)⁻¹) = 1
      rw [map_mul,map_inv,←hj]
      exact mul_inv_cancel _
    have hr := hker hx
    have hr' : ρ ((n:A) * (k j)⁻¹) = 1 := hr
    have heq := congrArg (fun f => f * ρ (k j)) hr'
    rw [←map_mul,inv_mul_cancel_right,one_mul] at heq
    exact ⟨j,heq⟩
  let kN : J →* N := k.codRestrict N (fun j => ⟨j,rfl⟩)
  let S : Subrepresentation τ := {
    toSubmodule := LinearMap.range ι
    apply_mem_toSubmodule n _ hv := by
      obtain ⟨y,rfl⟩ := hv
      obtain ⟨j,hj⟩ := same n
      exact ⟨σ j y, (he j y).trans (congrArg (fun f => f (ι y)) hj.symm)⟩ }
  have hsimple : IsIrreducible S.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom S).mpr
    rw [isAtom_iff_le_of_ge]
    refine ⟨?_,?_⟩
    · intro hbot
      obtain ⟨j,y,hy⟩ := hm
      have zero (z : Y) : ι z = 0 := by
        have hz : ι z ∈ S := ⟨z,rfl⟩
        rw [hbot] at hz
        exact hz
      exact hy (hi ((zero _).trans (zero _).symm))
    · intro R hR hRS
      let P : Subrepresentation σ := {
        toSubmodule := R.toSubmodule.comap ι
        apply_mem_toSubmodule j y hy := by
          change ι (σ j y) ∈ R
          rw [he]
          exact R.apply_mem_toSubmodule (kN j) hy }
      have hP : P ≠ ⊥ := by
        intro hp
        apply hR
        apply bot_unique
        intro x hx
        obtain ⟨y,rfl⟩ := hRS hx
        have hy : y ∈ P := hx
        rw [hp] at hy
        change y = 0 at hy
        rw [hy,map_zero]
        exact (⊥ : Subrepresentation τ).toSubmodule.zero_mem
      have hp := (hs.eq_bot_or_eq_top P).resolve_left hP
      rintro x ⟨y,rfl⟩
      exact (show y ∈ P from hp ▸ Submodule.mem_top)
  have hmove : ∃ n : N, ∃ x : S, S.toRepresentation n x ≠ x := by
    obtain ⟨j,y,hy⟩ := hm
    refine ⟨kN j,⟨ι y,⟨y,rfl⟩⟩,?_⟩
    intro hh
    have hh' : ρ (k j) (ι y) = ι y := congrArg Subtype.val hh
    rw [←he] at hh'
    exact hy (hi hh')
  have hf := fixedSpace_eq_bot_of_normal_simple_seed ρ N S hsimple hmove hgen
  intro x hx
  have hxN : x ∈ fixedSpace τ ⊤ := by
    intro n
    obtain ⟨j,hj⟩ := same n.val
    exact (congrArg (fun f => f x) hj).trans (hx j)
  change fixedSpace τ ⊤ = ⊥ at hf
  rw [hf] at hxN
  exact hxN

end Representation
