module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.Calculations
public import Theory.Representation.EndFieldFrobenius
public import Theory.Representation.EndFieldDegree
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.GroupEquivalence
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.InvertingCubic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SimpleFittingExtensions

/-!
# Scalar descent and cubic displacement for small binary J₂ modules

The trace relations x⁴ = x, with a trace not fixed by x ↦ x², force the
actual Schur field of an irreducible binary module to have degree two.
Absolute degrees 6 and 14 consequently give binary degrees 12 and 28.
In absolute degree 14, a cubic fixed space of dimension at most four gives
binary displacement at least twenty. Every involution inverts an automorphic
image of the same cubic generator, so the commutator rank inequality gives
involution displacement at least ten on the original ambient representation.
This includes outer involutions without assuming that they are F₄-linear.

The absolute catalogue, its trace relations, and the cubic fixed-space
calculation remain explicit premises below. They are separate mathematical
obligations; these conditional transports do not prove the J₂ catalogue.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.16, and Hiss--Malle's corrected low-degree tables (J₂ rows).
-/

public section
open scoped MonoidAlgebra
namespace Representation.JankoTwo.SmallBinaryDegrees
open Sporadic.LeechRelated.J2
open BinaryOffender Subgroup
universe v

variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

set_option backward.isDefEq.respectTransparency false in
/-- Exact field degree follows from traces, rather than a field-of-definition label. -/
theorem schur_degree_two_of_trace_relations
    (σ : Representation (ZMod 2) Carrier W) [σ.IsIrreducible]
    (hfour : ∀ g, σ.endFieldRep.character g ^ 4 = σ.endFieldRep.character g)
    (htwo : ∃ g, σ.endFieldRep.character g ^ 2 ≠ σ.endFieldRep.character g) :
    schurDegree 2 σ = 2 := by
  have hdiv : schurDegree 2 σ ∣ 2 :=
    (endFieldRep_trace_frobenius_iff 2 σ 2).mp (by simpa [Representation.character] using hfour)
  have hnot : ¬ schurDegree 2 σ ∣ 1 := by
    intro h
    have htrace := (endFieldRep_trace_frobenius_iff 2 σ 1).mpr h
    obtain ⟨g, hg⟩ := htwo
    exact hg (by simpa [Representation.character] using htrace g)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
  · exact (hnot (by simp [h])).elim
  · exact h

/-- The actual Schur model is six- or fourteen-dimensional over a quadratic
binary extension, conditional on the absolute catalogue calculations. -/
theorem schur_data_of_absolute_calculations
    (hcalc : AbsoluteWindowCalculations.{v})
    (σ : Representation (ZMod 2) Carrier W) (hf : Function.Injective σ)
    (hi : σ.IsIrreducible) (hd : Module.finrank (ZMod 2) W ≤ 32) :
    let := hi
    schurDegree 2 σ = 2 ∧
      (Module.finrank (Module.End (ZMod 2)[Carrier] σ.asModule) σ.asModule = 6 ∨
       Module.finrank (Module.End (ZMod 2)[Carrier] σ.asModule) σ.asModule = 14) := by
  let := hi
  let E := Module.End (ZMod 2)[Carrier] σ.asModule
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  obtain ⟨hdeg, hfour, htwo⟩ := hcalc E σ.asModule σ.endFieldRep
    ((endFieldRep_injective_iff σ).mpr hf) (endFieldRep_isAbsolutelyIrreducible σ)
    ((endField_finrank_le σ).trans hd)
  exact ⟨schur_degree_two_of_trace_relations σ hfour htwo, hdeg⟩

/-- Scalar descent of the absolute degree window, with the field calculation
included in the premise that must still be supplied. -/
theorem finrank_cases_of_absolute_calculations
    (hcalc : AbsoluteWindowCalculations.{v})
    (σ : Representation (ZMod 2) Carrier W) (hf : Function.Injective σ)
    (hi : σ.IsIrreducible) (hd : Module.finrank (ZMod 2) W ≤ 32) :
    Module.finrank (ZMod 2) W = 12 ∨ Module.finrank (ZMod 2) W = 28 := by
  let := hi
  obtain ⟨he, hdeg⟩ := schur_data_of_absolute_calculations hcalc σ hf hi hd
  have hdim := finrank_eq_endField_mul σ
  change Module.finrank (ZMod 2) W = schurDegree 2 σ * _ at hdim
  rw [he] at hdim
  rcases hdeg with hdeg | hdeg <;> simp only [hdeg] at hdim <;> omega

set_option backward.isDefEq.respectTransparency false in
/-- Absolute fixed dimension at most four becomes binary cubic displacement
at least twenty, on the original binary module. -/
theorem cubic_displacement_of_absolute_calculations
    (hcalc : AbsoluteWindowCalculations.{v}) (hcubic : CubicFixedSpaceCalculations.{v})
    (σ : Representation (ZMod 2) Carrier W) (hf : Function.Injective σ)
    (hi : σ.IsIrreducible) (hd : Module.finrank (ZMod 2) W = 28) :
    20 ≤ fixedCodim σ (zpowers GeneratorPair.b) := by
  let := hi
  let E := Module.End (ZMod 2)[Carrier] σ.asModule
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  obtain ⟨he, hdeg⟩ := schur_data_of_absolute_calculations hcalc σ hf hi (by omega)
  have hdim := finrank_eq_endField_mul σ
  change Module.finrank (ZMod 2) W = schurDegree 2 σ * Module.finrank E σ.asModule at hdim
  have habs : Module.finrank E σ.asModule = 14 := by rw [he, hd] at hdim; omega
  have hfix := hcubic E σ.asModule σ.endFieldRep
    ((endFieldRep_injective_iff σ).mpr hf) (endFieldRep_isAbsolutelyIrreducible σ) habs
  have htransfer := finrank_invariants_eq_endField_mul σ (zpowers GeneratorPair.b)
  change Module.finrank (ZMod 2) (fixedSpace σ (zpowers GeneratorPair.b)) =
    schurDegree 2 σ * _ at htransfer
  rw [he] at htransfer
  have hsum := fixedCodim_add_finrank σ (zpowers GeneratorPair.b)
  dsimp only [E] at hfix
  omega

section Inversion
variable {G : Type*} [Group G]

/-- Inverting an element of cube one bounds its displacement by twice that
of the inverter. No field linearity beyond F₂ is used. -/
theorem cubic_displacement_le_twice_of_inverts (ρ : Representation (ZMod 2) G W)
    (t c : G) (hc : c ^ 3 = 1) (hinv : t * c * t⁻¹ = c⁻¹) :
    fixedCodim ρ (zpowers c) ≤ 2 * fixedCodim ρ (zpowers t) := by
  have hinv2 : c⁻¹ * c⁻¹ = c := by
    apply mul_left_cancel (a := c * c)
    calc
      c * c * (c⁻¹ * c⁻¹) = 1 := by group
      _ = c * c * c := by simpa only [pow_succ, pow_two, pow_one, pow_zero, one_mul] using hc.symm
  have hcomm : t * c * t⁻¹ * c⁻¹ = c := by rw [hinv, hinv2]
  simpa only [hcomm] using fixedCodim_commutator_le_twice ρ t c

/-- A marking and the cubic estimate suffice for every ambient involution.
The generalized Fitting centralizer theorem keeps the original ambient G. -/
theorem involution_displacement_of_cubic_bound [Finite G]
    [IsSimpleGroup (Theory.GroupTheory.generalizedFitting G)]
    (ρ : Representation (ZMod 2) G W)
    (e : Theory.GroupTheory.generalizedFitting G ≃* Carrier)
    (hf : Function.Injective ρ)
    (hi : IsIrreducible (ρ.comp (Theory.GroupTheory.generalizedFitting G).subtype))
    (hcubic : ∀ σ : Representation (ZMod 2) Carrier W,
      Function.Injective σ → σ.IsIrreducible → 20 ≤ fixedCodim σ (zpowers GeneratorPair.b))
    (t : G) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    10 ≤ fixedCodim ρ (zpowers t) := by
  let L := Theory.GroupTheory.generalizedFitting G
  let r := ExceptionalParabolics.extensionEquivAut
    (SimpleFittingExtensions.ambientAction e t)
  have hr : orderOf r = 2 :=
    (orderOf_injective ExceptionalParabolics.extensionEquivAut.toMonoidHom
      ExceptionalParabolics.extensionEquivAut.injective
      (SimpleFittingExtensions.ambientAction e t)).trans
      ((orderOf_injective (SimpleFittingExtensions.ambientAction e)
        (SimpleFittingExtensions.ambientAction_injective e) t).trans
          (orderOf_eq_prime ht2 ht))
  obtain ⟨α, hα⟩ := InvertingCubic.exists_inverted_generator r hr
  let c : L := e.symm (α GeneratorPair.b)
  have hc : (c : G) ^ 3 = 1 := by
    have he : c ^ 3 = 1 := by
      dsimp [c]
      rw [← map_pow, ← map_pow, GeneratorPair.b_pow_three, map_one, map_one]
    exact congrArg Subtype.val he
  have hequiv : ExceptionalParabolics.intoExtension (r (e c)) =
      SimpleFittingExtensions.ambientAction e t * ExceptionalParabolics.intoExtension (e c) *
        (SimpleFittingExtensions.ambientAction e t)⁻¹ := by
    apply ExceptionalParabolics.extensionAction_injective
    simp only [map_mul, map_inv, ExceptionalParabolics.extensionAction_inner]
    exact (MulAut.congr_conj r (e c)).symm
  have hinv : t * (c : G) * t⁻¹ = (c : G)⁻¹ := by
    apply SimpleFittingExtensions.ambientAction_injective e
    simp only [map_mul, map_inv, SimpleFittingExtensions.ambientAction_on_fitting]
    rw [← hequiv]
    have hh : r (e c) = (e c)⁻¹ := by
      simpa only [c, MulEquiv.apply_symm_apply] using hα
    rw [hh, map_inv]
  let σ : Representation (ZMod 2) Carrier W := (ρ.comp L.subtype).comp (e.symm.toMonoidHom.comp α.toMonoidHom)
  have hσf : Function.Injective σ :=
    ((hf.comp L.subtype_injective).comp e.symm.injective).comp α.injective
  have hσi : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (e.symm.toMonoidHom.comp α.toMonoidHom)
      (e.symm.surjective.comp α.surjective) _).mpr hi
  have hbound := hcubic σ hσf hσi
  have hsame : fixedCodim σ (zpowers GeneratorPair.b) = fixedCodim ρ (zpowers (c : G)) := by
    rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
    rfl
  rw [hsame] at hbound
  have hle := cubic_displacement_le_twice_of_inverts ρ t c hc hinv
  omega

end Inversion
end Representation.JankoTwo.SmallBinaryDegrees
