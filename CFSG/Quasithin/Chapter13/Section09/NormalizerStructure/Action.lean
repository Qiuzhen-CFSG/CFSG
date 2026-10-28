module
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.Order
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.BGeneration

/-!
# The actual five-point normalizer quotient

Either candidate four-point class generates B. Hence the pointwise
centralizer of the five-point z-orbit is B. Orbit–stabilizer now makes
the literal permutation action surjective onto S5, and its kernel is
exactly B. The quotient equivalence retains the original conjugation
formula and the actual quotient map.

Source: Aschbacher–Smith 13.9.9, printed pp.972–973.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

omit [Finite G] in
theorem B_local_class_generates (b:Bool) :
    Subgroup.closure {x:G | x∈m.B ∧ x∈m.localInvolutionClass (if b then 4 else 2)}=m.B := by
  have he:{x:G | x∈m.B ∧ x∈m.localInvolutionClass (if b then 4 else 2)}=
      m.embedding '' {x:W | x∈SymmetricFourWreath.B ∧ IsConj (representative (if b then 4 else 2)) x} := by
    ext x
    constructor
    · rintro ⟨⟨a,ha,rfl⟩,hc⟩
      exact ⟨a,⟨ha,(m.embedding_mem_localInvolutionClass _ a).mp hc⟩,rfl⟩
    · rintro ⟨a,⟨ha,hc⟩,rfl⟩
      exact ⟨mem_map_of_mem m.embedding ha,(m.embedding_mem_localInvolutionClass _ a).mpr hc⟩
  rw [he,←MonoidHom.map_closure,B_class_generates]
  rfl

theorem normalizerOrbit_generating_class {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∃b:Bool,m.fusionFlags (if b then 4 else 2)=true := by
  have h0:m.fusionFlags 0=true := by
    simp only [fusionFlags,decide_eq_true_eq]
    exact IsConj.refl _
  have h1:m.fusionFlags 1=false := by
    simp only [fusionFlags,decide_eq_false_iff_not]
    exact fun h=>m.not_isConj_t_z h.symm
  have h3:m.fusionFlags 3=false := by
    simp only [fusionFlags,decide_eq_false_iff_not]
    intro h
    exact m.not_isConj_t_z ((m.double_transposition_fused_t (hG.evenCharacteristic d.T)
      (m.centralizer_growth hG).1).trans h.symm)
  have hc:=m.normalizerOrbit_card_flags
  rw [m.normalizerOrbit_card_five hG,classFlagCard_eq,h0,h1,h3] at hc
  cases h2:m.fusionFlags 2 <;> cases h4:m.fusionFlags 4
  · simp [h2,h4] at hc
  · exact ⟨true,h4⟩
  · exact ⟨false,h2⟩
  · exact ⟨false,h2⟩

theorem normalizerOrbit_pointwise_centralizer {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    centralizer {x:G | x∈m.B ∧ IsConj m.z x}=m.B := by
  apply le_antisymm
  · obtain ⟨b,hb⟩:=m.normalizerOrbit_generating_class hG
    have hf:IsConj m.z (m.embedding (representative (if b then 4 else 2))) := by
      simpa only [fusionFlags,decide_eq_true_eq] using hb
    have hsub:{x:G | x∈m.B ∧ x∈m.localInvolutionClass (if b then 4 else 2)}⊆
        {x:G | x∈m.B ∧ IsConj m.z x} := by
      intro x hx
      exact ⟨hx.1,hf.trans (m.isConj_of_mem_localInvolutionClass _ x hx.2)⟩
    have h:=centralizer_le hsub
    have he:centralizer {x:G | x∈m.B ∧ x∈m.localInvolutionClass (if b then 4 else 2)}=m.B := by
      rw [←centralizer_closure,m.B_local_class_generates,m.centralizer_B (hG.evenCharacteristic d.T)]
    exact h.trans he.le
  · calc
      m.B = centralizer (m.B:Set G) := (m.centralizer_B (hG.evenCharacteristic d.T)).symm
      _ ≤ _ := centralizer_le (fun _ h=>h.1)

theorem normalizerOrbitAction_kernel {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    m.normalizerOrbitAction.ker=m.B.subgroupOf (normalizer (m.B:Set G)) := by
  rw [m.normalizerOrbitAction_ker,m.normalizerOrbit_pointwise_centralizer hG]

def normalizerFiveCoordinates {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    m.normalizerOrbit≃Fin 5 :=
  (Finite.equivFin _).trans (finCongr (m.normalizerOrbit_card_five hG))

def normalizerS5Action {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    normalizer (m.B:Set G)→*Equiv.Perm (Fin 5) :=
  (m.normalizerFiveCoordinates hG).permCongrHom.toMonoidHom.comp m.normalizerOrbitAction

theorem normalizerS5Action_kernel {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    (m.normalizerS5Action hG).ker=m.B.subgroupOf (normalizer (m.B:Set G)) := by
  rw [normalizerS5Action,MonoidHom.ker_comp_of_injective _ _
    (m.normalizerFiveCoordinates hG).permCongrHom.injective,m.normalizerOrbitAction_kernel hG]

theorem normalizerS5Action_surjective {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    Function.Surjective (m.normalizerS5Action hG) := by
  have hk:Nat.card (m.normalizerS5Action hG).ker=16 := by
    rw [m.normalizerS5Action_kernel hG,
      Nat.card_congr (subgroupOfEquivOfLe m.B.le_normalizer).toEquiv]
    exact m.card_elementaryGroup false false
  have he:=(m.normalizerS5Action hG).ker.card_mul_index
  rw [index_ker,hk,m.normalizer_card_1920 hG] at he
  have hc:Nat.card (m.normalizerS5Action hG).range=120 := by omega
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  rw [hc,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  decide

def normalizerQuotientS5 {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    (normalizer (m.B:Set G)⧸m.B.subgroupOf (normalizer (m.B:Set G)))≃*Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq (m.normalizerS5Action_kernel hG).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (m.normalizerS5Action hG) (m.normalizerS5Action_surjective hG))

theorem normalizerS5Action_apply {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (g:normalizer (m.B:Set G)) (x:m.normalizerOrbit) :
    m.normalizerS5Action hG g (m.normalizerFiveCoordinates hG x)=
      m.normalizerFiveCoordinates hG (m.normalizerOrbitAction g x) := by
  change m.normalizerFiveCoordinates hG
    (m.normalizerOrbitAction g ((m.normalizerFiveCoordinates hG).symm
      (m.normalizerFiveCoordinates hG x)))=_
  rw [Equiv.symm_apply_apply]

omit [Finite G] in
theorem normalizerOrbitAction_apply_coe (g:normalizer (m.B:Set G)) (x:m.normalizerOrbit) :
    ((m.normalizerOrbitAction g x).val:G)=(g:G)*(x.val:G)*(g:G)⁻¹ := rfl

theorem normalizerQuotientS5_mk {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (g:normalizer (m.B:Set G)) :
    m.normalizerQuotientS5 hG (QuotientGroup.mk g)=m.normalizerS5Action hG g := rfl

end CFSG.Quasithin.Chapter13.Section09.Marking
