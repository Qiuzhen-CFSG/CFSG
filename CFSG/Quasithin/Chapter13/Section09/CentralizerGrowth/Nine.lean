module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.NotFive
public import Theory.SpecificGroups.SymmetricFourWreath.OrthogonalB.Flags

/-!
# The original nine-point normalizer orbit

The native class flags have sizes1,2,4,4,4,0. Excluding the axis classes and orbit sizes one and five forces nine and both diagonal four-point classes.

Source: Aschbacher–Smith 13.9.5, printed pp.970–971 (PDF pp.987–988).
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)

noncomputable def fusionFlags (i:Fin 6) : Bool := by
  classical
  exact decide (IsConj m.z (m.embedding (representative i)))

noncomputable def BParametersEquiv : Parameters ≃* m.B :=
  parametersEquivB.trans (m.imageEquiv SymmetricFourWreath.B)

omit [Finite G] in
private theorem parameters_fusionFlags (a:Parameters) :
    IsConj m.z (m.BParametersEquiv a:G) ↔ a≠1 ∧ m.fusionFlags (parameterIndex a)=true := by
  classical
  change IsConj m.z (m.embedding (parametersToW a)) ↔ _
  by_cases ha:a=1
  · subst a
    simp only [map_one,ne_eq,not_true_eq_false,false_and]
    rw [iff_false]
    intro hc
    have he : m.z=1 := by simpa using hc
    have ho := m.z_order
    rw [he,orderOf_one] at ho
    omega
  · have ho : orderOf (parametersToW a)=2 := by
      rw [orderOf_injective parametersToW parametersToW_injective]
      exact orderOf_eq_prime ((by decide +kernel : ∀a:Parameters,a^2=1) a) ha
    have hc := m.embedding.map_isConj ((isConj_representative_iff (parameterIndex a) _).mpr
      ⟨ho,parametersToW_index a⟩)
    simp only [ha,ne_eq,not_false_eq_true,true_and,fusionFlags,decide_eq_true_eq]
    exact ⟨fun h=>h.trans hc.symm,fun h=>h.trans hc⟩

theorem normalizerOrbit_card_flags : m.normalizerOrbit.ncard=classFlagCard m.fusionFlags := by
  classical
  let e : {a:Parameters // a≠1 ∧ m.fusionFlags (parameterIndex a)=true} ≃ m.normalizerOrbit :=
    m.BParametersEquiv.toEquiv.subtypeEquiv (fun a=>
      (m.parameters_fusionFlags a).symm.trans (m.mem_normalizerOrbit_iff_isConj (m.BParametersEquiv a)).symm)
  rw [←Nat.card_coe_set_eq,←Nat.card_congr e,Nat.card_eq_fintype_card]
  rfl

theorem normalizerOrbit_nine_of_centralizer_eq
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    m.normalizerOrbit.ncard=9 ∧ m.fusionFlags 3=true ∧ m.fusionFlags 4=true := by
  have h0 : m.fusionFlags 0=true := by
    simp only [fusionFlags,decide_eq_true_eq]
    exact IsConj.refl _
  have h1 : m.fusionFlags 1=false := by
    simp only [fusionFlags,decide_eq_false_iff_not]
    exact m.not_isConj_z_representative_of_centralizer_eq hC 1 (Or.inl rfl)
  have h2 : m.fusionFlags 2=false := by
    simp only [fusionFlags,decide_eq_false_iff_not]
    exact m.not_isConj_z_representative_of_centralizer_eq hC 2 (Or.inr (Or.inl rfl))
  rw [m.normalizerOrbit_card_flags]
  apply classFlagCard_nine m.fusionFlags h0 h1 h2
  · rw [←m.normalizerOrbit_card_flags]
    exact m.normalizerOrbit_card_ne_one_of_centralizer_eq hG hC
  · rw [←m.normalizerOrbit_card_flags]
    exact m.normalizerOrbit_card_ne_five_of_centralizer_eq hG hC

theorem conjugate_z_local_classes_iff_of_centralizer_eq
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) (x:G) (hx:x∈d.M) :
    IsConj m.z x ↔ x∈m.localInvolutionClass 0 ∨
      x∈m.localInvolutionClass 3 ∨ x∈m.localInvolutionClass 4 := by
  have hn := m.normalizerOrbit_nine_of_centralizer_eq hG hC
  have h3 : IsConj m.z (m.embedding (representative 3)) := by
    simpa only [fusionFlags,decide_eq_true_eq] using hn.2.1
  have h4 : IsConj m.z (m.embedding (representative 4)) := by
    simpa only [fusionFlags,decide_eq_true_eq] using hn.2.2
  refine ⟨m.conjugate_z_local_classes_of_centralizer_eq hC x hx,?_⟩
  rintro (⟨g,_,hg⟩|⟨g,_,hg⟩|⟨g,_,hg⟩)
  · exact isConj_iff.mpr ⟨g,hg⟩
  · exact h3.trans (isConj_iff.mpr ⟨g,hg⟩)
  · exact h4.trans (isConj_iff.mpr ⟨g,hg⟩)
end CFSG.Quasithin.Chapter13.Section09.Marking
