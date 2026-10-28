module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceG2Cover
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceFiltration

/-!
# The G₂ source exclusion after the parabolic estimates

The recognized natural component section produces the entire natural/Weyl
module and hence the upper bound m(U_H)≤8. Abelianness of the original V_H
places it in H_C, while faithfulness identifies the literal critical kernel
Dγ. Applying the source filtration gives the contradiction from the three
parabolic contributions and Dγ≰H_C. Thus no dimension, whole-module cover,
filtration, or conjugacy premise remains in this consumer.

Recognition of the natural section and the four parabolic estimates are still
earlier inputs. In particular this conditional consumer is not an unconditional
proof of 13.8.27. Source: Aschbacher–Smith, printed p.963, final paragraph.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceG2Exclusion
open TransvectionRecognition TransvectionRecognition.Component
open AlternatingAndLinear.FourStructure.CriticalTransfer
open CriticalGeometry

variable {G : Type*} [Group G] [Finite G] {L T H V V₃ V₁ K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [IsElementaryAbelian 2 (Source.VH H V)]
  [((Source.UH H V₃).subgroupOf H).Normal]

/-- Apply the proved cover and filtration deductions to the same source
quotients and critical pair. Only section recognition and the parabolic lower
estimates remain beyond the earlier source geometry and commutator generation. -/
theorem source_exclusion_of_section
    (c : CriticalPair L T H V) (hV : V ≤ H) (hV₃ : V₃ ≤ V)
    (hline : V₁ ≤ Source.UH H V₃) (hcard : Nat.card V₁ = 2)
    (hz : H ≤ centralizer (V₁ : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (Atlas.G2.Natural.OrthogonalCover.binaryNatural (ZMod 2)) eK)
    (hUg : c.Ugamma V₃ ≤ H)
    (hDC : ¬ Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ≤ Source.HC H V₃)
    (ha : 2 ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hm : 3 ≤ rank
      (((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.VH H V).subgroupOf H).map
        (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf H))))
    (hb : 3 ≤ rank (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.UH H V₃)) :
    False := by
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
  have hVC : Source.VH H V ≤ Source.HC H V₃ := by
    refine le_inf (conjugateSpanBy_le_self hV) ?_
    exact (Source.VH H V).le_centralizer.trans (centralizer_le hUV)
  exact SourceFiltration.contradiction_of_source_bounds c ρ s
    (faithful_of_centralizer_le_core ρ hρ hcentralizer) hUg hUV hVC hDC ha hm hb
    (SourceG2Cover.rank_le_eight_of_section hKH hK ρ hρ hgen eK hs hline hcard)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceG2Exclusion
end
