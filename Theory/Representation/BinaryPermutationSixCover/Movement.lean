module
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# Movement bounds for marked six-letter covers

Both permitted models project onto the same natural four-space. This proves
faithfulness under an injective marking and places their fixed codimension
between the natural and augmentation-core values. Every transport retains
the caller's six-letter homomorphism.

Source: Aschbacher–Smith I.1.5–6 and 14.6.22(1), with the paired-cover
application in original 14.6.24(2), printed p.1041.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace BinaryPermutation.SixCover
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- Every marked natural or augmentation cover maps onto the same marked
natural quotient. -/
theorem IsNaturalOrCore.natural_quotient
    {ρ : Representation (ZMod 2) H U} {e : H →* Equiv.Perm (Fin 6)}
    (h : IsNaturalOrCore ρ e) :
    ∃ p : U →ₗ[ZMod 2] natural (Fin 6), Function.Surjective p ∧
      ∀ g v, p (ρ g v) = naturalRepresentation (Fin 6) (e g) (p v) := by
  rcases h with ⟨E,hE⟩ | ⟨E,hE⟩
  · exact ⟨E.toLinearMap,E.surjective,hE⟩
  · refine ⟨(coreToNatural (Fin 6)).comp E.toLinearMap,
      coreToNatural_surjective.comp E.surjective,?_⟩
    intro g v
    change coreToNatural (Fin 6) (E (ρ g v)) = _
    rw [hE,coreToNatural_equivariant]
    rfl

/-- An injective six-letter marking makes either cover faithful. -/
theorem IsNaturalOrCore.injective
    {ρ : Representation (ZMod 2) H U} {e : H →* Equiv.Perm (Fin 6)}
    (h : IsNaturalOrCore ρ e) (he : Function.Injective e) : Function.Injective ρ := by
  obtain ⟨p,hp,hact⟩ := h.natural_quotient
  intro a b hab
  apply he
  apply naturalRepresentation_injective (Fin 6) (by decide)
  ext v
  obtain ⟨u,rfl⟩ := hp v
  rw [←hact,←hact,hab]

/-- The movement of a cover lies between that of its natural quotient and
that of the full augmentation cover, with the same actor marking. -/
theorem IsNaturalOrCore.fixedCodim_bounds
    {ρ : Representation (ZMod 2) H U} {e : H →* Equiv.Perm (Fin 6)}
    (h : IsNaturalOrCore ρ e) (A : Subgroup H) :
    fixedCodim (naturalRepresentation (Fin 6)) (A.map e) ≤ fixedCodim ρ A ∧
      fixedCodim ρ A ≤ fixedCodim (coreRepresentation (Fin 6)) (A.map e) := by
  have hcn : fixedCodim (naturalRepresentation (Fin 6)) (A.map e) ≤
      fixedCodim (coreRepresentation (Fin 6)) (A.map e) :=
    fixedCodim_le_of_equivariant_surjection _ _ (coreToNatural (Fin 6))
      coreToNatural_surjective (fun g v => coreToNatural_equivariant g v) _
  rcases h with ⟨E,hE⟩ | ⟨E,hE⟩
  · rw [fixedCodim_map_equivariant ρ (naturalRepresentation (Fin 6)) e E hE A]
    exact ⟨le_rfl,hcn⟩
  · rw [fixedCodim_map_equivariant ρ (coreRepresentation (Fin 6)) e E hE A]
    exact ⟨hcn,le_rfl⟩

end BinaryPermutation.SixCover
