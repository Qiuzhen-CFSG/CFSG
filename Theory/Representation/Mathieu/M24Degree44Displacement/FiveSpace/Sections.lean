module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Exterior
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.Averaging
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility

/-!
# Order-five fixed-space bounds inherited by binary sections

Odd-order averaging makes the map from an invariant subspace onto its section
surjective on fixed vectors. Consequently a section has no more fixed
dimensions than the ambient module. In dimension 44 an order-five fixed
dimension is divisible by four, so an ambient bound of eleven improves to
eight. No irreducibility, module classification or absolute scalar field is
needed for this linear step.

Source: the order-five argument of Guralnick--Malle, Classification of
2F-modules I, Proposition 5.1, manuscript p.17.
-/

public section
namespace Representation.MathieuM24Degree44.FiveSpace
open BinaryOffender

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Odd-order fixed dimensions cannot increase on a literal subquotient. -/
theorem IsSectionOf.fixed_finrank_le [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}
    (h : IsSectionOf ρ σ) (A : Subgroup G) [Finite A] (hA : Odd (Nat.card A)) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) ≤
      Module.finrank (ZMod 2) (fixedSpace σ A) := by
  obtain ⟨S, f, hf⟩ := h
  have hsurj := finrank_fixedSpace_surjection_of_odd S.toRepresentation ρ f.toLinearMap
    (fun g v => LinearMap.congr_fun (f.isIntertwining' g) v) hf A hA
  have hsub := Submodule.finrank_mono
    (inf_le_right : S.toSubmodule ⊓ fixedSpace σ A ≤ fixedSpace σ A)
  rw [← (subrepresentationFixedEquiv σ S A).finrank_eq] at hsub
  omega

/-- Divisibility excludes the possible fixed dimensions nine, ten and eleven. -/
theorem fixed_finrank_le_eight_of_le_eleven [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hd : Module.finrank (ZMod 2) V = 44)
    (x : G) (hx : orderOf x = 5)
    (h : Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers x)) ≤ 11) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers x)) ≤ 8 := by
  have hm := four_dvd_fixedCodim_of_order_five ρ x hx
  have hs := fixedCodim_add_finrank ρ (Subgroup.zpowers x)
  omega

/-- A degree-44 section inherits the required eight-dimensional bound. -/
theorem IsSectionOf.five_fixed_finrank_le_eight [FiniteDimensional (ZMod 2) V]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}
    (h : IsSectionOf ρ σ) (hd : Module.finrank (ZMod 2) V = 44)
    (x : G) (hx : orderOf x = 5)
    (hσ : Module.finrank (ZMod 2) (fixedSpace σ (Subgroup.zpowers x)) ≤ 11) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers x)) ≤ 8 := by
  have hc : Nat.card (Subgroup.zpowers x) = 5 := by rw [Nat.card_zpowers, hx]
  let : Finite (Subgroup.zpowers x) := Nat.finite_of_card_ne_zero (by omega)
  apply fixed_finrank_le_eight_of_le_eleven ρ hd x hx
  exact (h.fixed_finrank_le (Subgroup.zpowers x) (by rw [hc]; decide)).trans hσ

end Representation.MathieuM24Degree44.FiveSpace
