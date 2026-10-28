module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SixSymmetry

/-!
# The marked actor calculation at every eligible critical pair

This adapter supplies the exact uniform actor implication consumed by
`SixSymmetry.six_factor_reversal` and `SixSymmetry.source_six_factor_strict`.
The eligible pair provides its noncyclic actor and an actual H-conjugator
into the edge two-core. Inverting that witness matches the convention of
`source_sixActorFacts`; the common source seed and natural heads then prove
rank two and offender absence on the fixed exterior-square chief section.
Thus the implication applies also to the constructed reversed pair.

Only earlier geometry, seed data, natural heads and the equivariant section
identification are inputs. The intrinsic model bounds are already proved.
The subsequent symmetry and chief-factor exclusion remain with their owners.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed p.961 (PDF p.978), using 13.8.8(2) and 13.8.18(4).
-/

public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
open Alignment CriticalTransfer CriticalGeometry CriticalGeometry.Reorientation

variable {G U : Type*} [Group G] [Finite G]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {L T H V V₃ V₁ : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- Discharge the complete `hactor` premise of the six-factor reversal and
strict-inclusion arguments, uniformly over their eligible critical pairs.
No actor rank-two or offender-exclusion premise remains. -/
theorem source_eligible_sixActorFacts
    [IsElementaryAbelian 2 (Source.VH H V)]
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hV₃ : V₃ ≤ V)
    (L₀ L₁ : Subgroup G) (hL : L₀ ≤ L₁) (hPH : L₁ ⊔ T ≤ H)
    (hthree : Nat.card (L₀ ⧸ pCore 2 L₀) = 3) (hfix : ⁅L₀, V₃⁆ ≤ V₁)
    (hT : IsPGroup 2 T)
    (hstable : ∀ a : Source.starImage H (L₁ ⊔ T), ∀ v ∈ s.image V₃,
      ρ a v ∈ s.image V₃)
    (hirr : IsAtom (⟨s.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ T)).subtype)))
    (hdim : Module.finrank (ZMod 2) (s.image V₃) = 2)
    (hgeo : ∀ c : CriticalPair L T H V, EarlierGeometry c V₃ V₁)
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (hheads : AllNaturalHeads ρ eH)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (X Y : Subrepresentation ρ) :
    ∀ c : CriticalPair L T H V, SixSymmetry.Eligible L₁ V₃ V₁ ρ c →
      X ⋖ Y → Y ≤ W → ¬ IsCentralSection ρ X Y →
      IsExteriorSquare (sectionRepresentation ρ X Y) eH →
      SixActorFacts ρ X Y (Source.starImage H (c.Ugamma V₃))
        (Source.starImage H c.Vgamma) := by
  intro c hc _ _ _ hsix
  obtain ⟨h, _, hplace⟩ := hc.placement
  apply source_sixActorFacts c s hV₃ (hgeo c).VH_endpoint (hgeo c).Vgamma_H
    hc.noncyclic L₀ L₁ hL hPH hthree hfix hT hstable hirr hdim eH hheads
    W hW h⁻¹ _ X Y hsix
  simpa only [InvMemClass.coe_inv, inv_inv] using hplace

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
