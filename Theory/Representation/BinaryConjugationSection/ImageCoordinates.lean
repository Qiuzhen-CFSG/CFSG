module
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Coordinates on a subgroup with an injectively marked full image

If an injective intertwiner has image equal to the entire coordinate image
of B, invert its range equivalence on B. The resulting section keeps the
original central kernel and recovers the original coordinate map pointwise.
No complement to the kernel is selected.

The normal field-four support application uses this to mark the literal
[U_J,K]/Z by the five-point augmentation module, before studying the action
on [U_J,K] itself. Source: the section correspondence in Aschbacher--Smith
14.6.22 and the permutation-module argument of 14.3.6(1), printed pp.1038,991.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H V}
  {σ : Representation (ZMod 2) H W}

/-- An injectively marked full image gives coordinates on the original subgroup. -/
theorem exists_of_image_eq_range (c : BinaryConjugationSection H U Z ρ)
    (B : Subgroup G) (hBU : B ≤ U) (hZB : Z ≤ B)
    (hNB : H ≤ normalizer (B : Set G))
    (i : W →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (hact : ∀ h w, i (σ h w) = ρ h (i w))
    (himage : c.imageSpace B = LinearMap.range i) :
    ∃ d : BinaryConjugationSection H B Z σ,
      ∀ b : B, i (d.coordinates b).toAdd = (c.coordinates (inclusion hBU b)).toAdd := by
  let E := LinearEquiv.ofInjective i hi
  let f : B →* Multiplicative (LinearMap.range i) := {
    toFun b := Multiplicative.ofAdd
      ⟨(c.coordinates (inclusion hBU b)).toAdd,
        himage ▸ ((c.mem_imageSpace_iff B _).mpr ⟨inclusion hBU b,b.property,rfl⟩)⟩
    map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one c.coordinates)
    map_mul' b b' := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (map_mul c.coordinates (inclusion hBU b) (inclusion hBU b')) }
  let q : B →* Multiplicative W :=
    E.symm.toAddEquiv.toMultiplicative.toMonoidHom.comp f
  have hq (b : B) : i (q b).toAdd = (c.coordinates (inclusion hBU b)).toAdd :=
    congrArg Subtype.val (E.apply_symm_apply (f b).toAdd)
  refine ⟨{ section_le := hBU.trans c.section_le
            kernel_le := hZB
            normalized := hNB
            coordinates := q
            onto := ?_
            kernel_eq := ?_
            equivariant := ?_ },hq⟩
  · intro w
    have hw : i w.toAdd ∈ c.imageSpace B := himage.symm ▸ ⟨w.toAdd,rfl⟩
    obtain ⟨u,hu,he⟩ := (c.mem_imageSpace_iff B _).mp hw
    refine ⟨⟨u,hu⟩,Multiplicative.toAdd.injective (hi ?_)⟩
    exact (hq ⟨u,hu⟩).trans he
  · ext b
    change q b = 1 ↔ ((inclusion hBU b : U) : G) ∈ Z
    rw [←c.coordinates_eq_one_iff (inclusion hBU b)]
    change (q b).toAdd = 0 ↔ (c.coordinates (inclusion hBU b)).toAdd = 0
    rw [←hq,LinearMap.map_eq_zero_iff i hi]
  · intro h b
    apply hi
    rw [hq,hact,hq]
    exact c.equivariant h (inclusion hBU b)
end Representation.BinaryConjugationSection
