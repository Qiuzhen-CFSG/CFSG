module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversalIndices
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.NaturalLowerBound
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ConjugateSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.DualLowerBound
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData

/-!
# Consequences of the L₄ critical pair

The leaves prove the irreducible codimension bound in both natural and
contragredient cases, the exact denominator and rank identities for the
inverse conjugator, and transport of the actual central section to the other
endpoint. This module assembles those leaves with the genuine source data.
The equality case uses the normalized reversed graph pair, including its
actor-specific module and nonsplitting data, and exports the resulting fixed
space containment.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed p.962, and Remark F.9.17, printed p.324.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
open CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences

universe u v w

variable {G : Type u} {U : Type v} [Group G] [Finite G]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {L T H V V₃ V₁ : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-! The common endpoint data used by the dual branch are deliberately explicit.
The upper quotient is the actual `V_H/U_H` section and `hgen` is the source
generation conclusion for this actor; neither is inferred from a family tag. -/

theorem critical_section_codimension_ge_two_of_source
    [IsElementaryAbelian 2 (Source.VH H V)]
    (S : SourceData L T H V V₃ V₁ ρ) (c : CriticalPair L T H V)
    (hc : Eligible S c)
    (hcomm : Coinvariants.ker
        (S.N.toRepresentation.comp (Source.starImage H (c.Ugamma V₃)).subtype) =
      Coinvariants.ker
        (S.N.toRepresentation.comp (Source.starImage H c.Vgamma).subtype))
    {E : Type w} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (VH : Subgroup G) (τ : Representation (ZMod 2) (Source.Hstar H) E)
    (t : UpperSection H VH (Source.UH H V₃) τ)
    (X : Subgroup G) (hXV : X ≤ VH)
    (hspan : VH = conjugateSpanBy X H)
    (hindex : (Source.UH H V₃).relIndex X = 2)
    (P : Submodule (ZMod 2) ChiefFactors.NaturalSpace)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hparabolic : ∀ a : H,
      S.eH (QuotientGroup.mk' (pCore 2 H) a) ∈ BinaryLinear.parabolic P →
        (a : G) ∈ normalizer (X : Set G))
    (g : G) (B : Subgroup G)
    (hJ : vertexGroup L T H c.gamma = H.map (MulAut.conj g).toMonoidHom)
    (hUg : c.Ugamma V₃ = (Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
    (hVg : c.Vgamma = VH.map (MulAut.conj g).toMonoidHom)
    (hZ : Nat.card V₁ = 2)
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔ B)
    (hedge : ⁅B, X.map (MulAut.conj g).toMonoidHom⁆ ≤ c.Ugamma V₃)
    (hnoncentral : ¬ ⁅H, VH⁆ ≤ Source.UH H V₃) :
    2 ≤ Module.finrank (ZMod 2)
      (S.N.toSubmodule ⧸
        (S.sectionModel.image (Source.DH (Source.UH H V₃)
          (c.Ugamma V₃) (c.Aone V₁))).comap S.N.toSubmodule.subtype) := by
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) := by
    apply hc.endpoint_le.trans
    rw [c.vertexGroup_gamma]
    exact (S.sectionModel.centralizes_conjugate_line (c.gb : G)).trans
      (centralizer_le_normalizer _)
  have hA : Nat.card (c.Aone V₁) = 2 := by
    rw [CriticalPair.Aone, card_map_of_injective (MulAut.conj _).injective,
      S.line_card]
  rcases S.natural_irreducible with hNat | ⟨e, he⟩
  · exact critical_section_codimension_ge_two_of_same_natural_head
      S.sectionModel S.I (vertexGroup L T H c.gamma) (c.Ugamma V₃)
      c.Vgamma (c.Aone V₁) S.line_le_I S.I_le S.N S.W S.image_I
      hc.Ugamma_le hc.Vgamma_le hc.endpoint_le hUA
      (S.endpoint_centralizer c) hA hc.line_not_le hc.noncyclic S.eH hNat
      ⟨S.head, S.head_equivariant⟩ hc.axes
  · exact critical_section_codimension_ge_two_of_dual S.sectionModel S.I
      (vertexGroup L T H c.gamma) (c.Ugamma V₃) c.Vgamma (c.Aone V₁)
      S.line_le_I S.I_le S.N S.image_I hc.Vgamma_le hc.endpoint_le hUA
      (S.endpoint_centralizer c) hA hc.line_not_le S.eH e he hc.quadratic hcomm
      VH τ t X hXV hspan hindex P hP hparabolic g B hJ hUg hVg hZ hgen hedge
      hnoncentral

/-! Equality is used only after the actual reversed geodesic has been built.
The output contains both the desired noncontainment and the fixation needed
by the central quotient argument. -/

theorem equality_case_noncontainment_and_fixation
    [IsElementaryAbelian 2 (Source.VH H V)]
    (S : SourceData L T H V V₃ V₁ ρ) (c : CriticalPair L T H V)
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ V₁)
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (generation18 : ∀ d : CriticalPair L T H V,
      ∀ F ≤ Source.UH H V₃,
      ¬ F ≤ Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone V₁) →
      vertexGroup L T H d.gamma =
        conjugateSpanBy F (vertexGroup L T H d.gamma) ⊔
          edgeGroup L T H d.gamma d.previous)
    (hrank : 1 < rank (Source.starImage H (c.Ugamma V₃)))
    (hequal : Module.finrank (ZMod 2)
      (U ⧸ S.sectionModel.image (Source.DH (Source.UH H V₃)
        (c.Ugamma V₃) (c.Aone V₁))) =
      rank (Source.starImage H (c.Ugamma V₃))) :
    ¬ c.Aone V₁ ≤ Source.UH H V₃ ∧
      S.sectionModel.image (Source.DH (Source.UH H V₃)
        (c.Ugamma V₃) (c.Aone V₁)) ≤
        fixedSpace ρ (Source.starImage H (c.Ugamma V₃)) := by
  obtain ⟨r, hr, hline⟩ := exists_eligible_reversal V₃ V₁ S c hgeo hcore generation18
    hrank hequal
  have hnot : ¬ c.Aone V₁ ≤ Source.UH H V₃ := by
    intro hA
    exact (hr.forward) (hline.mpr hA)
  have hUV : Source.UH H V₃ ≤ Source.VH H V :=
    conjugateSpanBy_mono S.seed_le le_rfl
  have hUend : Source.UH H V₃ ≤ vertexGroup L T H c.gamma :=
    hUV.trans (hgeo c).VH_endpoint
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) := by
    apply hUend.trans
    rw [c.vertexGroup_gamma]
    exact (S.sectionModel.centralizes_conjugate_line (c.gb : G)).trans
      (centralizer_le_normalizer _)
  have hA : Nat.card (c.Aone V₁) = 2 := by
    rw [CriticalPair.Aone, card_map_of_injective (MulAut.conj _).injective,
      S.line_card]
  exact ⟨hnot, S.sectionModel.critical_fixed_of_line_not_le
    (c.Ugamma V₃) (c.Aone V₁) hUA hA hnot⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
