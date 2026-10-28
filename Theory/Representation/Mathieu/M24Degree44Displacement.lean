module

public import Theory.Representation.Mathieu.M24Degree44Displacement.Inputs
public import Theory.Representation.Mathieu.M24Degree44Displacement.Geometry
public import Theory.Representation.Mathieu.M24Degree44Displacement.Inversion
public import Theory.Representation.Mathieu.M24Degree44Displacement.Cover

/-!
# Degree-44 involution displacement from the order-five calculation

Every involution of native M₂₄ inverts an order-five element. A fixed space
of dimension at most eight for that element gives displacement at least 36;
the commutator rank bound gives displacement at least eighteen for the
involution. Faithfulness and irreducibility remove arbitrary central covers,
with the original vector space and literal action retained throughout.

Only the order-five representation calculation remains an explicit premise.
This conditional reduction does not prove that calculation or GM02's theorem.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, author manuscript p.17.
-/

public section
namespace Representation.MathieuM24Degree44
open Subgroup Theory.GroupTheory BinaryOffender Sporadic.Mathieu
universe u v
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The order-five calculation gives the required native involution bound. -/
theorem native_displacement_of_fiveFixedSpaceBound (hfive : FiveFixedSpaceBound.{v})
    (ρ : Representation (ZMod 2) M24 V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) (hd : Module.finrank (ZMod 2) V = 44)
    (t : M24) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    18 ≤ fixedCodim ρ (zpowers t) := by
  obtain ⟨x, hx, htx⟩ := M24Degree44Displacement.exists_inverted_five t ht ht2
  have hfix := hfive ρ hf hi hd x hx
  have hdim := fixedCodim_add_finrank ρ (zpowers x)
  have hmove := fixedCodim_five_le_twice_of_inverts ρ t x hx htx
  omega

/-- The native calculation applies to every allowed cover through its specified quotient. -/
theorem cover_displacement_of_fiveFixedSpaceBound (hfive : FiveFixedSpaceBound.{v})
    {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    (ρ : Representation (ZMod 2) L V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) (e : L ⧸ center L ≃* M24)
    (hd : Module.finrank (ZMod 2) V = 44) (t : L) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    18 ≤ fixedCodim ρ (zpowers t) := by
  let f := modelEquiv ρ hf hi e
  let σ : Representation (ZMod 2) M24 V := ρ.comp f.symm.toMonoidHom
  have hσf : Function.Injective σ := hf.comp f.symm.injective
  have hσi : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff f.symm.toMonoidHom f.symm.surjective ρ).mpr hi
  have hft : f t ≠ 1 := fun h => ht (f.injective (h.trans (map_one f).symm))
  have hft2 : f t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have h := native_displacement_of_fiveFixedSpaceBound hfive σ hσf hσi hd (f t) hft hft2
  rwa [fixedCodim_comp_equiv_symm] at h

end Representation.MathieuM24Degree44
