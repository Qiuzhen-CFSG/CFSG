module
public import Theory.Representation.SL2FourNaturalExtensions.SylowElements
public import Theory.Representation.BinaryOffender.QuadraticFixedDimension
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Natural-by-natural binary SL₂(4) extensions

Let X be an invariant submodule of a finite binary SL₂(4)-module Y, with both
X and the literal quotient Y/X equivariantly identified with the standard
natural module. If a full Sylow two-subgroup fixes at least four dimensions
of Y, then it acts quadratically. No splitting of the extension is assumed.

Each nonidentity Sylow element has fixed codimension two on both sections.
The submodule–quotient inequality gives ambient fixed codimension at least
four. Since Y has dimension eight, its element fixed space has dimension at
most four. Equality with the common fixed space forces quadratic action.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 3.4, printed
pp.37–39, specialized to characteristic two and field order four. The
cardinality form is the terminal module input after the Main Hypothesis
argument constructs Y=Q/Z(H), X=Z(Q)/Z(H), and the two natural sections.
The construction of those group sections remains a separate hypothesis.
-/

public section
noncomputable section
namespace Representation.SL2FourNaturalExtensions
open Subgroup BinaryOffender SL2FourNatural
variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
  [FiniteDimensional (ZMod 2) Y]

/-- A natural-by-natural binary extension is quadratic for a full Sylow
two-subgroup whose fixed space has dimension at least four. -/
theorem sylow_isQuadratic_of_natural_sections
    (ρ : Representation (ZMod 2) SL Y) (X : Subrepresentation ρ)
    (eX : X.toSubmodule ≃ₗ[ZMod 2] V)
    (eQ : (Y ⧸ X.toSubmodule) ≃ₗ[ZMod 2] V)
    (heX : ∀ g x, eX (X.toRepresentation g x) = naturalRepresentation g (eX x))
    (heQ : ∀ g x, eQ (X.quotientRepresentation g x) = naturalRepresentation g (eQ x))
    (P : Sylow 2 SL) (hfixed : 4 ≤ Module.finrank (ZMod 2) (fixedSpace ρ P)) :
    IsQuadratic ρ P := by
  have hX : Module.finrank (ZMod 2) X.toSubmodule = 4 :=
    eX.finrank_eq.trans finrank_vector
  have hQ : Module.finrank (ZMod 2) (Y ⧸ X.toSubmodule) = 4 :=
    eQ.finrank_eq.trans finrank_vector
  have hY : Module.finrank (ZMod 2) Y = 8 := by
    have := X.toSubmodule.finrank_quotient_add_finrank
    omega
  apply isQuadratic_of_fixedDimension_bound ρ P
    (fun g hg => (sylow_element_natural P hg).1) 4 ?_ hfixed
  intro g hg hn
  have hgdim := (sylow_element_natural P hg).2 hn
  have hXdim : fixedCodim X.toRepresentation (zpowers g) = 2 := by
    have := fixedCodim_map_equivariant X.toRepresentation naturalRepresentation
      (MonoidHom.id SL) eX heX (zpowers g)
    simpa only [Subgroup.map_id, hgdim] using this
  have hQdim : fixedCodim X.quotientRepresentation (zpowers g) = 2 := by
    have := fixedCodim_map_equivariant X.quotientRepresentation naturalRepresentation
      (MonoidHom.id SL) eQ heQ (zpowers g)
    simpa only [Subgroup.map_id, hgdim] using this
  have := fixedCodim_quotient_add_subrepresentation_le ρ X (zpowers g)
  have := fixedCodim_add_finrank ρ (zpowers g)
  omega

/-- The fixed-space cardinality form used in the terminal binary branch of
Niles's Main Hypothesis argument. The submodule and quotient are literal. -/
theorem sylow_isQuadratic_of_natural_sections_card
    (ρ : Representation (ZMod 2) SL Y) (X : Subrepresentation ρ)
    (eX : X.toSubmodule ≃ₗ[ZMod 2] V)
    (eQ : (Y ⧸ X.toSubmodule) ≃ₗ[ZMod 2] V)
    (heX : ∀ g x, eX (X.toRepresentation g x) = naturalRepresentation g (eX x))
    (heQ : ∀ g x, eQ (X.quotientRepresentation g x) = naturalRepresentation g (eQ x))
    (P : Sylow 2 SL) (hfixed : Nat.card (fixedSpace ρ P) = 16) :
    IsQuadratic ρ P := by
  apply sylow_isQuadratic_of_natural_sections ρ X eX eQ heX heQ P
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ P)
  rw [hfixed, Nat.card_eq_fintype_card, ZMod.card] at hc
  have he : 4 = Module.finrank (ZMod 2) (fixedSpace ρ P) :=
    Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc
  omega

end Representation.SL2FourNaturalExtensions
