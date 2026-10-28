module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.Earlier
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.AssemblySupport

/-!
# From recognized component sections to every conclusion of 13.8.5

Apply the universal earlier 13.7.6 to the actual component section. The
linear-map model is first transported to the genuine projective matrix
model. In degree four the resulting H* identification lifts to H=KT,
using the Sylow subgroup to absorb O₂(H).

For alternating sections, 13.7.6 supplies commutator generation and the
set product. Subnormal supplement theory now proves component normality.
The concrete covering constructions give the entire natural or augmentation
module, and the transvection selects the full symmetric actor. Finally the
order-two fixed kernel transfers the two chief factors from U_H to U_H/V₁.
The local quotient equivalences are retained in their respective branches.

This is the conditional section-to-model contract: the recognized section
and universal earlier theorems are inputs. Component selection and G.6.4,
and proofs of the universal earlier theorems, are not asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.7.6(1),(3), pp.938–940; I.1.5–6, p.408; 13.8.5, pp.947–948.
-/

@[expose] public section
open Subgroup Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open RecognitionStep
variable {G : Type*} [Group G] [Finite G] {H K V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

omit [Finite G] in
/-- Applicability of the source linear clause uses the actual PSL comparison,
including equivariance on every representative of the component section. -/
theorem projective_section_of_linear
    (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (n : ℕ) (hn : 0 < n)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin n → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation n) eK) :
    HasSectionModel H V₃ V₁ ρ K hKH (projectiveRepresentation n hn)
      (eK.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear hn).symm) := by
  obtain ⟨hstable, e, he⟩ := hs
  refine ⟨hstable, e, ?_⟩
  intro k u
  simpa only [projectiveRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using he k u

/-- All source alternatives for the specified recognized component. The only
earlier inputs are universal statements; every specialization, full alternating
module, normality assertion and chief-series quotient passage is constructed. -/
theorem full_alternatives_of_recognized_section
    (T : Sylow 2 G) {L V V₂ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (t : Source.Hstar H) (ht : IsTransvection ρ t)
    (hs : RecognizedSection H K V₃ V₁ hKH ρ) :
    let := d.uh_elementary hH
    (H : Set G) = (K : Set G) * (T : Set G) ∧
      FullAlternatives H L (sourceOne L T V₁) V₃ V₁ (le_sup_left.trans hH.1.2) ρ := by
  let := d.uh_elementary hH
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hcentralizer := (earlier.centralizer d H hH).le
  rcases hs with ⟨n, hn, eK, hs⟩ | ⟨n, hn, eK, hs⟩
  · have hp := projective_section_of_linear hKH ρ n (by omega) eK hs
    obtain ⟨rfl, ⟨eH, eV, heV⟩, hL⟩ := earlier.linear d H hH ρ hρ K hKH hK n hn
      (eK.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega)).symm) hp
    have hprod := product_of_equiv_component_quotient T hTH hKH hK
      (eH.trans ((BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)).trans eK.symm))
    exact ⟨hprod, Or.inr ⟨Or.inr ⟨eH, eV, heV⟩, hL⟩⟩
  · obtain ⟨hgen, _hLK, hprod, hcases⟩ := earlier.alternating d H hH ρ hρ K hKH hK n hn eK hs
    rcases hcases with ⟨rfl, hL, hchief⟩ | ⟨rfl, hL⟩
    · have hchief' := ChiefQuotient.twoNoncentralChiefFactors_utilde H V₃ V₁
        (sourceOne L T V₁) (le_sup_left.trans hH.1.2) ρ hρ (d.line_le_uh H) d.line_card hchief
      have hnormal := component_normal_of_product T hTH hKH hK hprod
      rcases alternatingSix_full_module_of_section hKH hK hnormal ρ hρ hcentralizer
        hgen eK hs t ht with ⟨eH, eV, _heK, heV⟩ | ⟨eH, eV, _heK, heV⟩
      · exact ⟨hprod, Or.inl ⟨Or.inl ⟨eH, eV, heV⟩, hL, hchief'⟩⟩
      · have hdim : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 5 :=
          eV.finrank_eq.trans (BinaryPermutation.finrank_core (Fin 6))
        exact ⟨hprod, Or.inl ⟨Or.inr ⟨⟨eH, eV, heV⟩, hdim⟩, hL, hchief'⟩⟩
    · obtain ⟨eH, eV, _heK, heV⟩ := alternatingSeven_full_module_of_section
        T hTH hKH hK hprod ρ hρ hcentralizer hgen eK hs t ht
      exact ⟨hprod, Or.inr ⟨Or.inl ⟨eH, eV, heV⟩, hL⟩⟩

/-- The component is also returned inside H, exactly as required by 13.8.5(1).
The remaining two clauses are the linked full-actor module alternatives. -/
theorem complete_conclusions_of_recognized_section
    (T : Sylow 2 G) {L V V₂ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (t : Source.Hstar H) (ht : IsTransvection ρ t)
    (hs : RecognizedSection H K V₃ V₁ hKH ρ) :
    let := d.uh_elementary hH
    (∃ C : Subgroup H, C.IsCComponent ∧
      (H : Set G) = (C.map H.subtype : Set G) * (T : Set G)) ∧
      FullAlternatives H L (sourceOne L T V₁) V₃ V₁ (le_sup_left.trans hH.1.2) ρ := by
  obtain ⟨hprod, hmodels⟩ := full_alternatives_of_recognized_section T d earlier hH hKH hK ρ hρ t ht hs
  refine ⟨⟨K.subgroupOf H, hK, ?_⟩, hmodels⟩
  rwa [map_subgroupOf_eq_of_le hKH]

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
end
