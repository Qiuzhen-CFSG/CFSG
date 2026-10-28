module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.Application
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.FaithfulDisplacement

/-!
# The faithful middle section in the source G₂ exclusion

The literal point-parabolic actor has rank two. On the actual faithful
V_H/U_H section, dual offender exclusion gives displacement at least three,
without a natural-module identification. The original middle-image transport
then places this contribution in the canonical H/U_H quotient. Together with
the bottom estimate and supplied core movement, this applies the source
filtration contradiction.

Parabolic marking and core motion remain explicit and are retained by
qt-d-138-g2-parabolic-estimates; final source assembly is
qt-d-138-six-g2-source. This theorem discharges the faithful displacement
premise only. Source: Aschbacher–Smith 13.8.27, printed p.963.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open TransvectionRecognition TransvectionRecognition.Component
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry
open Atlas.G2

variable {G X Y : Type*} [Group G] [Finite G]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  {L T H V V₃ V₁ K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [IsElementaryAbelian 2 (Source.VH H V)]
  [((Source.UH H V₃).subgroupOf H).Normal]

/-- The source application with the arbitrary faithful-module displacement
proved from the fitting equality and the literal component isomorphism. -/
theorem source_exclusion_of_faithful_point_parabolic
    (c : CriticalPair L T H V) (hV : V ≤ H) (hV₃ : V₃ ≤ V)
    (hline : V₁ ≤ Source.UH H V₃) (hcard : Nat.card V₁ = 2)
    (hz : H ≤ centralizer (V₁ : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Model (ZMod 2)))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (Natural.OrthogonalCover.binaryNatural (ZMod 2)) eK)
    (hUg : c.Ugamma V₃ ≤ H)
    (hreverse : Source.VH H V ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hVQ : Source.VH H V ≤ Source.QH H)
    (f : Source.Hstar H →* Model (ZMod 2)) (hf : Function.Injective f)
    (p : Additive (Source.Utilde H V₃ V₁) →ₗ[ZMod 2] Natural.Space (ZMod 2))
    (hp : Function.Surjective p)
    (he : ∀ a v, p (ρ a v) = Natural.action (ZMod 2) (f a) (p v))
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hr : rank (Source.starImage H (c.Ugamma V₃)) < 3)
    (hAu : (Source.starImage H (c.Ugamma V₃)).map f ≤ unipotent)
    (hn : BinaryParabolicPair.derivedSecondAmbient ≤
      normalizer ((Source.starImage H (c.Ugamma V₃)).map f : Set _))
    (hH : H = centralizer (V₁ : Set G))
    (τ : Representation (ZMod 2) (Source.Hstar H) Y)
    (tQ : BinaryConjugationSection H (Source.QH H) (Source.HC H V₃)
      (τ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hcoremove : ∃ a ∈ Source.starImage H (c.Ugamma V₃),
      ∃ v ∈ tQ.imageSpace (Source.QH H ⊓ centralizer (c.Aone V₁ : Set G)), τ a v ≠ v)
    (σ : Representation (ZMod 2) (Source.Hstar H) X)
    (t : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃)
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hσ : Function.Injective σ)
    (hfit : Theory.GroupTheory.generalizedFitting (Source.Hstar H) = Source.starImage H K) : False := by
  let s : ConjugationSection H (Source.UH H V₃) V₁ ρ := {
    le := conjugateSpanBy_le_self (hV₃.trans hV)
    normalizes := le_normalizer_conjugateSpanBy V₃ H
    centralizes := hz
    line_le := hline
    quotient := {
      toFun := fun u => Multiplicative.ofAdd (Additive.ofMul
        (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    surjective := QuotientGroup.mk'_surjective _
    kernel := QuotientGroup.ker_mk' _
    conjugates := hρ }
  have hfaith := faithful_of_centralizer_le_core ρ hρ hcentralizer
  have hUV : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono hV₃ le_rfl
  obtain ⟨ha, hb⟩ := source_actor_and_bottom_bounds c s hfaith hUg
    (hUV.trans hreverse) (hUV.trans hVQ) f hf p hp he hA hr hAu hn
  have hDC := source_Dgamma_not_le_of_core_movement c s hfaith hUg hH τ tQ hcoremove
  have hmove := faithful_displacement_ge_three_of_fitting σ (Source.starImage H K)
    hfit hσ ((Components.componentStarEquiv H K hKH hK).symm.trans eK) hA ha
  have hm := hmove.trans (source_middle_displacement_le c s hfaith hUg hreverse hVQ σ t)
  exact SourceG2Exclusion.source_exclusion_of_section c hV hV₃ hline hcard hz
    hKH hK ρ hρ hcentralizer hgen eK hs hUg hDC ha.ge hm hb

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
end
