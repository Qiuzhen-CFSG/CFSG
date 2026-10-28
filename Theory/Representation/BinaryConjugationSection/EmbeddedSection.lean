module
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Embedded submodules of literal binary conjugation sections

An equivariant linear embedding pulls back to an actual subgroup of the
original section. Its coordinates retain the original kernel and action;
the quotient image is exactly the specified embedded submodule.
This is used for the natural and dual supports in Aschbacher--Smith
14.6.24(3), printed p.1041.
-/

@[expose] public noncomputable section
namespace Representation.BinaryConjugationSection
open Subgroup
variable {G E V : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup V] [Module (ZMod 2) V] {H U Z A : Subgroup G}
  {ρ : Representation (ZMod 2) H E}

/-- Restrict the actor while retaining the whole original section. -/
def restrictActor (c : BinaryConjugationSection H U Z ρ)
    (hAH : A ≤ H) (hUA : U ≤ A) :
    BinaryConjugationSection A U Z (ρ.comp (inclusion hAH)) where
  section_le := hUA
  kernel_le := c.kernel_le
  normalized := hAH.trans c.normalized
  coordinates := c.coordinates
  onto := c.onto
  kernel_eq := c.kernel_eq
  equivariant a u := c.equivariant (inclusion hAH a) u

/-- The invariant image of the specified embedding. -/
def embeddedSubrepresentation (σ : Representation (ZMod 2) H V)
    (e : V →ₗ[ZMod 2] E)
    (he : ∀ a v, ρ a (e v) = e (σ a v)) : Subrepresentation ρ where
  toSubmodule := e.range
  apply_mem_toSubmodule a := by
    rintro _ ⟨v,rfl⟩
    exact ⟨σ a v, (he a v).symm⟩

/-- The actual preimage of an embedded module, with its original coordinates. -/
def embeddedSection (c : BinaryConjugationSection H U Z ρ)
    (σ : Representation (ZMod 2) H V) (e : V →ₗ[ZMod 2] E)
    (hi : Function.Injective e) (he : ∀ a v, ρ a (e v) = e (σ a v)) :
    BinaryConjugationSection H
      (c.invariantPreimage (embeddedSubrepresentation σ e he)) Z σ := by
  let P := embeddedSubrepresentation σ e he
  let d := c.invariantSection P
  let q : V ≃ₗ[ZMod 2] P.toSubmodule := LinearEquiv.ofInjective e hi
  exact {
    section_le := d.section_le
    kernel_le := d.kernel_le
    normalized := d.normalized
    coordinates := q.symm.toAddEquiv.toMultiplicative.toMonoidHom.comp d.coordinates
    onto := q.symm.toAddEquiv.toMultiplicative.surjective.comp d.onto
    kernel_eq := by
      ext u
      change q.symm (d.coordinates u).toAdd = 0 ↔ (u : G) ∈ Z
      rw [q.symm.map_eq_zero_iff]
      exact d.coordinates_eq_one_iff u
    equivariant a u := by
      apply q.injective
      change q (q.symm (d.coordinates _).toAdd) =
        q (σ a (q.symm (d.coordinates u).toAdd))
      rw [q.apply_symm_apply]
      apply Subtype.ext
      change (d.coordinates _).toAdd.val = e (σ a (q.symm (d.coordinates u).toAdd))
      rw [←he]
      have hq : e (q.symm (d.coordinates u).toAdd) = (d.coordinates u).toAdd.val :=
        congrArg Subtype.val (q.apply_symm_apply (d.coordinates u).toAdd)
      rw [hq]
      exact congrArg Subtype.val (d.equivariant a u) }

theorem embeddedSection_coordinates (c : BinaryConjugationSection H U Z ρ)
    (σ : Representation (ZMod 2) H V) (e : V →ₗ[ZMod 2] E)
    (hi : Function.Injective e) (he : ∀ a v, ρ a (e v) = e (σ a v))
    (u : c.invariantPreimage (embeddedSubrepresentation σ e he)) :
    e ((c.embeddedSection σ e hi he).coordinates u).toAdd =
      (c.coordinates ⟨u,c.invariantPreimage_le _ u.property⟩).toAdd := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e hi).apply_symm_apply _)

theorem imageSpace_embeddedPreimage (c : BinaryConjugationSection H U Z ρ)
    (σ : Representation (ZMod 2) H V) (e : V →ₗ[ZMod 2] E)
    (he : ∀ a v, ρ a (e v) = e (σ a v)) :
    c.imageSpace (c.invariantPreimage (embeddedSubrepresentation σ e he)) = e.range := by
  apply le_antisymm
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := (c.mem_imageSpace_iff _ v).mp hv
    exact (c.mem_invariantPreimage _ u).mp hu |>.choose_spec
  · intro v hv
    obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
    refine (c.mem_imageSpace_iff _ v).mpr ⟨u,?_,hu⟩
    exact (c.mem_invariantPreimage _ u).mpr ⟨u.property,by rw [hu]; exact hv⟩
end Representation.BinaryConjugationSection
