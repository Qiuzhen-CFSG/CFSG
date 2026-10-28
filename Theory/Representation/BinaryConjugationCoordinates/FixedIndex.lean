module
public import Theory.Representation.BinaryConjugationCoordinates
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex

/-!
# Fixed indices in prescribed binary conjugation coordinates

A multiplicative module marking identifies the ambient centralizer index
with the power of two given by the model's fixed codimension. Compose the
inverse marking with the literal subgroup embedding and apply the embedded
fixed-index theorem. The actor marking need not be faithful.

This complements model_card_range, which computes the actor-side index.
The original mixed reciprocal application retains both indices in
Chapter13 Section04 FixedCoreSource/Nonsolvable/MixedLinearIndices.
Source: Aschbacher--Smith 13.4.15, printed p.912.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryConjugationCoordinates
variable {G Q M : Type*} [Group G] [Group Q]
  [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

/-- The module-side centralizer index in the prescribed coordinates. -/
theorem model_fixed_index
    (A U : Subgroup G) (hAU : A ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) Q M) (φ : A →* Q)
    (e : U ≃* Multiplicative M)
    (he : ∀ (a : A) (u : U),
      (e (U.normalizerMonoidHom ⟨a.val,hAU a.property⟩ u)).toAdd =
        σ (φ a) (e u).toAdd) :
    (centralizer (A : Set G)).relIndex U = 2 ^ fixedCodim σ φ.range := by
  let j := U.subtype.comp e.symm.toMonoidHom
  have hj : j.range = U := by
    ext u
    constructor
    · rintro ⟨v,rfl⟩
      exact (e.symm v).property
    · intro hu
      exact ⟨e ⟨u,hu⟩,congrArg Subtype.val (e.symm_apply_apply _)⟩
  apply embedded_centralizer_index σ U A j
    (U.subtype_injective.comp e.symm.injective) hj φ
  intro a v
  have hh := congrArg (fun w : M => (e.symm (Multiplicative.ofAdd w)).val)
    (he a (e.symm (Multiplicative.ofAdd v)))
  change (e.symm (e (U.normalizerMonoidHom ⟨a.val,hAU a.property⟩
    (e.symm (Multiplicative.ofAdd v))))).val =
    (e.symm (Multiplicative.ofAdd (σ (φ a) (e (e.symm (Multiplicative.ofAdd v))).toAdd))).val at hh
  rw [e.symm_apply_apply,e.apply_symm_apply] at hh
  exact hh.symm
end BinaryConjugationCoordinates
