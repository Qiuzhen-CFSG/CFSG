module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.PairedApplication
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.Marking.Source

/-!
# The G₂ parabolic contradiction from the earlier source geometry

The recognized literal component section constructs the whole-star natural
projection. The critical comparison places A₁ inside U_H and keeps its
natural image nonzero. Correcting lifts with Q_H identifies the actual
line-centralizer image with the point stabilizer. Relative normality then
identifies the critical actor with the long-root four-group. The original
commutator pairing and the arbitrary faithful V_H/U_H action supply the
remaining two filtration estimates, yielding the source contradiction.

Only independent earlier-source and component-recognition inputs remain;
there are no local marking, displacement, or moved-vector premises. Their
final discharge belongs to qt-d-138-six-g2-source.
Source: Aschbacher–Smith 13.8.27, final paragraph, printed p.963.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open TransvectionRecognition TransvectionRecognition.Component
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry
open Atlas.G2

variable {G X : Type*} [Group G] [Finite G]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  {L T H V V₃ V₁ K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [IsElementaryAbelian 2 (Source.VH H V)]
  [((Source.UH H V₃).subgroupOf H).Normal]

omit [IsElementaryAbelian 2 (Source.VH H V)] in
/-- The four geometric inputs to the literal source filtration, all on the
same critical pair and canonical quotient map. -/
theorem source_parabolic_estimates_of_section
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
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hB : IsElementaryAbelian 2 (Source.starImage H c.Vgamma))
    (hproper : Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma)
    (hH : H = centralizer (V₁ : Set G))
    (hcompare : Nat.log 2
      ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃)) ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hcomm : ⁅Source.QH H, Source.UH H V₃⁆ ≤ V₁)
    (hpluskernel : commutatorPreimage H (Source.UH H V₃)
      (Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G)) = Source.QH H)
    (σ : Representation (ZMod 2) (Source.Hstar H) X)
    (t : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃)
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hσ : Function.Injective σ)
    (hfit : Theory.GroupTheory.generalizedFitting (Source.Hstar H) = Source.starImage H K) :
    (¬ Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ≤ Source.HC H V₃) ∧
    2 ≤ rank (Source.starImage H (c.Ugamma V₃)) ∧
    3 ≤ rank (((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓
      Source.VH H V).subgroupOf H).map
        (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf H))) ∧
    3 ≤ rank (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.UH H V₃) := by
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
  have hUV : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono hV₃ le_rfl
  obtain ⟨hr, hAone, f, p, hf, hp, he, _, hAu, hn⟩ := source_point_marking_of_section
    c hKH hK hfit ρ hρ s hgen eK hs hUg (hUV.trans hreverse) hcard hcompare
    hA hB hproper hH hcomm hpluskernel
  have hfaith := faithful_of_centralizer_le_core ρ hρ hcentralizer
  obtain ⟨ha,hb⟩ := source_actor_and_bottom_bounds c s hfaith hUg
    (hUV.trans hreverse) (hUV.trans hVQ) f hf p hp he hA hr hAu hn
  have hDC := source_Dgamma_not_le_of_pairing c ρ s hfaith hUg hH hcard
    (hUV.trans hVQ) hAone hcomm hcentralizer hpluskernel hKH hK hfit eK hA ha
  have hmove := faithful_displacement_ge_three_of_fitting σ (Source.starImage H K)
    hfit hσ ((Components.componentStarEquiv H K hKH hK).symm.trans eK) hA ha
  exact ⟨hDC,ha.ge,hmove.trans
    (source_middle_displacement_le c s hfaith hUg hreverse hVQ σ t),hb⟩

/-- Exclude the recognized G₂ component using the original critical pair,
central commutator comparison, and faithful V_H/U_H section. -/
theorem source_exclusion_of_earlier_geometry
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
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hB : IsElementaryAbelian 2 (Source.starImage H c.Vgamma))
    (hproper : Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma)
    (hH : H = centralizer (V₁ : Set G))
    (hcompare : Nat.log 2
      ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃)) ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hcomm : ⁅Source.QH H, Source.UH H V₃⁆ ≤ V₁)
    (hpluskernel : commutatorPreimage H (Source.UH H V₃)
      (Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G)) = Source.QH H)
    (σ : Representation (ZMod 2) (Source.Hstar H) X)
    (t : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃)
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hσ : Function.Injective σ)
    (hfit : Theory.GroupTheory.generalizedFitting (Source.Hstar H) = Source.starImage H K) : False := by
  obtain ⟨hDC,ha,hm,hb⟩ := source_parabolic_estimates_of_section c hV hV₃ hline hcard hz
    hKH hK ρ hρ hcentralizer hgen eK hs hUg hreverse hVQ hA hB hproper
    hH hcompare hcomm hpluskernel σ t hσ hfit
  exact SourceG2Exclusion.source_exclusion_of_section c hV hV₃ hline hcard hz
    hKH hK ρ hρ hcentralizer hgen eK hs hUg hDC ha hm hb

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
end
