module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourFitting
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticSylowCore

/-!
# Original Fitting containment and an outside component

The actual quintic group XT lies in C_G(Ω₁Z(T)) and contains T. Hence
O₂(M₁), which lies in T and is normal in M₁, lies in O₂(XT)=T_L O₂(LT).
The proved S-family trap now contains O₂,F(M₁) in M. Escape of O₂,F*(M₁)
then supplies a literal ambient C-component outside M, retaining its actual
quasisimple two-core quotient and characteristic-two property.

Source: Aschbacher--Smith 6.1.4, printed p.665.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ : Subgroup G} {n : ℕ}

/-- The source containment Q₁≤S follows from the actual quintic core identity. -/
theorem original_hermitian_comparison_core_le_inner_sylow
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2)) (hCM₁ : omegaCentralizer T ≤ M₁) :
    M₁.pCoreIn 2 ≤ ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨D,_,_,_,_,_,hXT⟩ := original_hermitian_quintic_torus h hout hm
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hQT : M₁.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM₁] using
      pCoreIn_le_sylow M₁ (T.subtype hTM₁)
  rw [←original_hermitian_quintic_sylow_core h hout hm]
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M₁) (hQT.trans le_sup_right)
    ((hXT.trans hCM₁).trans (M₁.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image M₁ (pCore 2 M₁))))

/-- The ordinary two-Fitting preimage is contained in M under the original
degree-four Hermitian source assumptions, with no core or E.6.26 premise. -/
theorem original_hermitian_fitting_preimage_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁) :
    (twoFittingCore M₁).map M₁.subtype ≤ M :=
  full_reduced_hermitian_fitting_le_of_core_le h hout hm (by decide) hM₁
    (sylow_le_omegaCentralizer.trans hCM₁)
    (original_hermitian_comparison_core_le_inner_sylow h hout hm hCM₁)

/-- The original orthogonal source produces an actual ambient C-component
of M₁ outside M, with its literal quotient and characteristic-two property. -/
theorem original_hermitian_exists_component_outside
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn M₁ ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ generalizedFitting K = pCore 2 K ∧ ¬ K ≤ M := by
  have hf := original_hermitian_fitting_preimage_le h hout hm hM₁ hCM₁
  have hg := full_reduced_hermitian_component_escape h hout hm (by decide) hM₁ hCM₁
  have hchar := h.simpleQTKE.evenCharacteristic T M₁ hM₁
    (sylow_le_omegaCentralizer.trans hCM₁)
  obtain ⟨K,hK,hq,hfit,hnot⟩ := exists_characteristicTwo_cComponent_outside
    (M.subgroupOf M₁) hchar (map_le_iff_le_comap.mp hf)
    (fun hh => hg (map_le_iff_le_comap.mpr hh))
  let K₁ := K.map M₁.subtype
  let e : K ≃* K₁ := K.equivMapOfInjective M₁.subtype M₁.subtype_injective
  have hmK : K₁.subgroupOf M₁ = K := comap_map_eq_self_of_injective M₁.subtype_injective K
  let := hq
  have hq₁ : IsQuasisimple (K₁ ⧸ pCore 2 K₁) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hc : centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
    rw [←hfit]
    exact centralizer_generalizedFitting_le K
  have hc₁ := (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hc
  exact ⟨K₁,⟨map_subtype_le _,hmK.symm ▸ hK⟩,hq₁,
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hc₁,
    fun hh => hnot (map_le_iff_le_comap.mp hh)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
