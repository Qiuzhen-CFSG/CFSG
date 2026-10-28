module

public import Theory.Representation.IrreducibleMovedPlaneSections
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.TransportedGeometry
public import Theory.Representation.Quotient

/-!
# Excluding the ten-dimensional binary linear-five module

The complete irreducible-module classification identifies both exterior powers,
without a faithfulness, absolute-irreducibility or chosen-model assumption.
The proved involution calculations give displacement three or four on either
model. Transport through the actual actor equivalence and the literal section
quotient contradicts the ambient displacement bound of two.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.21, printed p.924, and I.1.6(7), printed p.408. The exterior-model
classification and calculations are reused from the existing Theory modules.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TenDimensional
open Representation.SL5TenDimensional

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem involution_rank (ρ : Representation (ZMod 2) Group V)
    [IsIrreducible ρ] (hd : Module.finrank (ZMod 2) V = 10)
    (t : Group) (ht : t ^ 2 = 1) (hne : t ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 3 ∨
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 4 := by
  rcases Classification.identification_of_finrank_ten ρ hd with he | he
  · obtain ⟨e⟩ := he
    have he := RankTwo.finrank_movedSpace_transport ρ (exteriorAction 2)
      (MulEquiv.refl Group) e.toLinearEquiv e.toIntertwiningMap.isIntertwining t
    rcases SL5ExteriorSquare.involution_displacement_ranks t hne
      (by simpa only [pow_two] using ht) with h | h
    · exact Or.inl (he.trans h.2)
    · exact Or.inr (he.trans h.2)
  · obtain ⟨e⟩ := he
    have he := RankTwo.finrank_movedSpace_transport ρ (exteriorAction 3)
      (MulEquiv.refl Group) e.toLinearEquiv e.toIntertwiningMap.isIntertwining t
    rcases SL5ExteriorSquare.Duality.cube_involution_displacement_ranks t hne
      (by simpa only [pow_two] using ht) with h | h
    · exact Or.inl (he.trans h)
    · exact Or.inr (he.trans h)

variable {E : Type*} [_root_.Group E]

theorem involution_rank_of_equiv (ρ : Representation (ZMod 2) E V)
    [IsIrreducible ρ] (e : E ≃* Group) (hd : Module.finrank (ZMod 2) V = 10)
    (t : E) (ht : t ^ 2 = 1) (hne : t ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 3 ∨
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 4 := by
  let τ := ρ.comp e.symm.toMonoidHom
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr inferInstance
  have ht' : e t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hn' : e t ≠ 1 := fun hh => hne (e.injective (hh.trans (map_one e).symm))
  have hh := involution_rank τ hd (e t) ht' hn'
  change Module.finrank (ZMod 2) (LinearMap.range (ρ (e.symm (e t)) - 1)) = 3 ∨
    Module.finrank (ZMod 2) (LinearMap.range (ρ (e.symm (e t)) - 1)) = 4 at hh
  exact (e.symm_apply_apply t) ▸ hh

/-- A section of the original module cannot be a ten-dimensional irreducible
SL₅(2) module when its distinguished involution moves at most two dimensions.
The complete exterior-square/exterior-cube classification is discharged. -/
theorem not_ten_dimensional_section [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) E V) (U N : Subrepresentation ρ)
    (hi : IsIrreducible (sectionRepresentation ρ U N))
    (e : E ≃* Group) (t : E) (ht : t ^ 2 = 1) (hne : t ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) :
    Module.finrank (ZMod 2)
      (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) ≠ 10 := by
  intro hd
  let := hi
  have hbound := fixedCodim_section_le ρ U N (Subgroup.zpowers t)
  rw [fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at hbound
  change Module.finrank (ZMod 2)
    (LinearMap.range (sectionRepresentation ρ U N t - 1)) ≤
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) at hbound
  rcases involution_rank_of_equiv (sectionRepresentation ρ U N) e hd t ht hne with h | h
  · change Module.finrank (ZMod 2)
      (LinearMap.range (sectionRepresentation ρ U N t - 1)) ≤ _ at hbound
    omega
  · change Module.finrank (ZMod 2)
      (LinearMap.range (sectionRepresentation ρ U N t - 1)) ≤ _ at hbound
    omega

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TenDimensional
