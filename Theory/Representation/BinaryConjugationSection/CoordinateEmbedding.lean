module
public import Theory.Representation.BinaryConjugationSection.EmbeddedSection
public import Mathlib.Algebra.Module.ZMod

/-!
# Embeddings from the original section coordinates

For nested numerators with the same coordinate kernel, the smaller quotient
maps injectively into the larger quotient. Descending the original coordinate
maps gives the embedding, its exact image, and covariance under the common
actor. This retains the actual supports when assembling a natural--dual pair
inside the whole terminal module.

Source application: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1041.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G E V : Type*} [Group G]
  [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup V] [Module (ZMod 2) V]
  {H K U A Z : Subgroup G} {ρ : Representation (ZMod 2) H E}
  {σ : Representation (ZMod 2) K V}

/-- The original coordinate quotients of nested sections with the same kernel
induce an injective intertwiner, with exactly the smaller section as image. -/
theorem exists_coordinate_embedding
    (c : BinaryConjugationSection H U Z ρ)
    (d : BinaryConjugationSection K A Z σ) (hKH : K ≤ H) (hAU : A ≤ U) :
    ∃ e : V →ₗ[ZMod 2] E, Function.Injective e ∧
      (∀ a : A, e (d.coordinates a).toAdd = (c.coordinates (inclusion hAU a)).toAdd) ∧
      (∀ k v, ρ (inclusion hKH k) (e v) = e (σ k v)) ∧
      e.range = c.imageSpace A := by
  let q := c.coordinates.comp (inclusion hAU)
  have hk : d.coordinates.ker ≤ q.ker := by
    intro a ha
    exact (c.coordinates_eq_one_iff (inclusion hAU a)).mpr
      ((d.coordinates_eq_one_iff a).mp ha)
  let f : Multiplicative V →* Multiplicative E :=
    d.coordinates.liftOfSurjective d.onto ⟨q,hk⟩
  have hf (a : A) : f (d.coordinates a) = q a :=
    d.coordinates.liftOfRightInverse_comp_apply _ _ _ _
  let e : V →ₗ[ZMod 2] E := (AddMonoidHom.toMultiplicative.symm f).toZModLinearMap 2
  have he (a : A) : e (d.coordinates a).toAdd = (c.coordinates (inclusion hAU a)).toAdd := hf a
  have hi : Function.Injective e := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro v hv
    obtain ⟨a,ha⟩ := d.onto (Multiplicative.ofAdd v)
    have hv' : e (d.coordinates a).toAdd = 0 := ha.symm ▸ hv
    rw [he] at hv'
    have hz := (c.coordinates_eq_one_iff (inclusion hAU a)).mp hv'
    have hz' := (d.coordinates_eq_one_iff a).mpr hz
    change v = 0
    exact congrArg Multiplicative.toAdd (ha.symm.trans hz')
  refine ⟨e,hi,he,?_,?_⟩
  · intro k v
    obtain ⟨a,ha⟩ := d.onto (Multiplicative.ofAdd v)
    have ha' : (d.coordinates a).toAdd = v := congrArg Multiplicative.toAdd ha
    rw [←ha',he,←d.equivariant,he]
    exact (c.equivariant (inclusion hKH k) (inclusion hAU a)).symm
  · ext v
    constructor
    · rintro ⟨w,rfl⟩
      obtain ⟨a,rfl⟩ := d.onto (Multiplicative.ofAdd w)
      exact (c.mem_imageSpace_iff A _).mpr ⟨inclusion hAU a,a.property,(he a).symm⟩
    · intro hv
      obtain ⟨a,ha,rfl⟩ := (c.mem_imageSpace_iff A v).mp hv
      exact ⟨(d.coordinates ⟨a,ha⟩).toAdd,he ⟨a,ha⟩⟩
end Representation.BinaryConjugationSection
