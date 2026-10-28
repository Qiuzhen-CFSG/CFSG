module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix.Transport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix.Calculations
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.RadicalPlacement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.Lifting
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.PreliminaryGeometry


/-!
# The marked six-dimensional source actor

The common natural head identifies the actual image of V₃ with a plane.
The order-three quotient of L₀ and its fixation of the seed put the specified
13.8.8(2) conjugate Vα* in that plane's radical. Actual conjugation on U_H/V₁
proves quadraticity; this descends to the literal section Y/(X ∩ Y).
The exterior model calculation then gives rank two. Rank and best-offender
transport through the same conjugator exclude every subgroup of Uγ*.

This works for any eligible critical pair, including a constructed reversal,
and in fact for any exterior-square section: chiefness and Y ≤ W are not
needed in this local calculation. The fixed actor identification is the one
shared by the natural heads and the exterior-square section. The source
adapter consumes only the earlier clauses used in this argument: seed
invariance and irreducibility, the cubic L₀ quotient, radical placement from
13.8.8(2), and noncyclicity from 13.8.18(4). It neither assumes rank two nor
any offender exclusion for the source action.

`exteriorRadicalBounds`, proved in `MarkedSix.Calculations`, supplies the
intrinsic calculation. Thus `source_sixActorFacts`
discharges the model bounds and proves both actor conclusions from the
displayed earlier source inputs. The proof works directly on the exterior
square; it needs neither the deleted-permutation comparison nor a catalogue
premise. This proves the marked calculation used in 13.8.25, not the whole
chief-factor classification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed p.961 (PDF p.978), using 13.8.4(6), 13.8.8(2), 13.8.18(4), and
B.3.2(6), printed p.84. The subsequent numerical deductions are in
`SourceSix`; the classification assembly remains with the chief-factor owner.
-/

public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
open Alignment CriticalTransfer CriticalTransfer.MarkedGeometry CriticalGeometry

variable {G U : Type*} [Group G] [Finite G]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {L T H V V₃ V₁ : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- Source transport for every eligible critical pair. The earlier inputs
are the source seed, L₀'s cubic quotient, the actual 13.8.8(2) conjugator,
and 13.8.18(4)'s noncyclicity. Quadraticity is proved from the source
conjugation section, and the rank-two conclusion is not an input.
This explicit-bounds version separates the source transport from the model
calculation; `source_sixActorFacts` below discharges those bounds. -/
theorem source_sixActorFacts_of_radical_bounds
    (hb : ExteriorRadicalBounds)
    (c : CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hV₃ : V₃ ≤ V)
    (hVHend : Source.VH H V ≤ vertexGroup L T H c.gamma)
    (hVH : c.Vgamma ≤ H)
    (h18 : 1 < rank (Source.starImage H c.Vgamma))
    (L₀ L₁ : Subgroup G) (hL : L₀ ≤ L₁) (hPH : L₁ ⊔ T ≤ H)
    (hthree : Nat.card (L₀ ⧸ pCore 2 L₀) = 3) (hfix : ⁅L₀, V₃⁆ ≤ V₁)
    (hT : IsPGroup 2 T)
    (hstable : ∀ a : Source.starImage H (L₁ ⊔ T), ∀ v ∈ s.image V₃,
      ρ a v ∈ s.image V₃)
    (hirr : IsAtom (⟨s.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ T)).subtype)))
    (hdim : Module.finrank (ZMod 2) (s.image V₃) = 2)
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (hheads : AllNaturalHeads ρ eH)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (h : H)
    (h8 : c.Vgamma.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2)
    (X Y : Subrepresentation ρ)
    (hXY : IsExteriorSquare (sectionRepresentation ρ X Y) eH) :
    SixActorFacts ρ X Y (Source.starImage H (c.Ugamma V₃))
      (Source.starImage H c.Vgamma) := by
  obtain ⟨e, he⟩ := hheads W hW
  let seed := sourceGeneratingSeed s L₁ T hT hstable hirr hdim
  have hP := headPlane_finrank ρ seed W hW.1 e
  have hrad := source_radical_placement s L₀ L₁ T c.Vgamma hL hPH hthree hfix
    hT hstable hirr hdim W hW.1 eH e he h h8
  have hrad' : ((Source.starImage H c.Vgamma).map
      (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h⁻¹)).toMonoidHom).map
        eH.toMonoidHom ≤ BinaryLinear.radical (headPlane ρ seed W e) := by
    rw [← starImage_conjugate c.Vgamma hVH h⁻¹]
    exact hrad
  have hUV : Source.starImage H (c.Ugamma V₃) ≤ Source.starImage H c.Vgamma :=
    map_mono (subgroupOf_mono H (map_mono (conjugateSpanBy_mono hV₃ le_rfl)))
  exact sixActorFacts_of_conjugate_radical_bounds hb ρ X Y eH hXY
    (headPlane ρ seed W e) hP _ _ hUV (QuotientGroup.mk' (pCore 2 H) h⁻¹) hrad'
    (c.quadratic_star_on_Utilde V₃ V₁ s hV₃ hVHend).1 h18

/-- The marked six-dimensional actor calculation of 13.8.25. Rank two and
absence of best offenders on the literal section are conclusions. The
intrinsic exterior-square bounds are proved, and quadraticity and radical
placement are derived from the earlier source inputs at this critical pair.
The same statement therefore applies to a constructed reversal. -/
theorem source_sixActorFacts
    (c : CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hV₃ : V₃ ≤ V)
    (hVHend : Source.VH H V ≤ vertexGroup L T H c.gamma)
    (hVH : c.Vgamma ≤ H)
    (h18 : 1 < rank (Source.starImage H c.Vgamma))
    (L₀ L₁ : Subgroup G) (hL : L₀ ≤ L₁) (hPH : L₁ ⊔ T ≤ H)
    (hthree : Nat.card (L₀ ⧸ pCore 2 L₀) = 3) (hfix : ⁅L₀, V₃⁆ ≤ V₁)
    (hT : IsPGroup 2 T)
    (hstable : ∀ a : Source.starImage H (L₁ ⊔ T), ∀ v ∈ s.image V₃,
      ρ a v ∈ s.image V₃)
    (hirr : IsAtom (⟨s.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ T)).subtype)))
    (hdim : Module.finrank (ZMod 2) (s.image V₃) = 2)
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (hheads : AllNaturalHeads ρ eH)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (h : H)
    (h8 : c.Vgamma.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2)
    (X Y : Subrepresentation ρ)
    (hXY : IsExteriorSquare (sectionRepresentation ρ X Y) eH) :
    SixActorFacts ρ X Y (Source.starImage H (c.Ugamma V₃))
      (Source.starImage H c.Vgamma) :=
  source_sixActorFacts_of_radical_bounds exteriorRadicalBounds c s hV₃ hVHend hVH h18
    L₀ L₁ hL hPH hthree hfix hT hstable hirr hdim eH hheads W hW h h8 X Y hXY

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
