module
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.Action

/-!
The five-point z-orbit and ten-point t-orbit partition the nonidentity elements of the actual B. The two remaining four-point local classes have opposite fusion flags; their ordering is retained as an alternative. Source: Aschbacher–Smith 13.9.9, printed p.973.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

def normalizerTPoint:m.B:=⟨m.t,m.t_mem_B⟩
def normalizerTOrbit:Set m.B:=MulAction.orbit (normalizer (m.B:Set G)) m.normalizerTPoint

theorem mem_normalizerTOrbit_iff (x:m.B) : x∈m.normalizerTOrbit ↔ IsConj m.t (x:G) := by
  constructor
  · rintro ⟨g,hg⟩
    exact isConj_iff.mpr ⟨g,congrArg Subtype.val hg⟩
  · intro hc
    obtain ⟨g,hg,he⟩:=m.diagonal_controls_fusion false m.t_mem_B x.property hc
    exact ⟨⟨g,hg⟩,Subtype.ext he⟩

theorem normalizerTOrbit_complement {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    m.normalizerTOrbit=(Set.univ\{1})\m.normalizerOrbit := by
  ext x
  rw [m.mem_normalizerTOrbit_iff]
  change IsConj m.t (x:G) ↔ (True ∧ x≠1) ∧ x∉m.normalizerOrbit
  rw [m.mem_normalizerOrbit_iff_isConj]
  constructor
  · intro hc
    refine ⟨⟨trivial,?_⟩,fun hz=>m.not_isConj_t_z (hc.trans hz.symm)⟩
    intro he
    have ho:(x:G)=1:=congrArg Subtype.val he
    rw [ho] at hc
    exact m.t_ne_one (by simpa using hc)
  · rintro ⟨⟨_,hx⟩,hn⟩
    have hxG:(x:G)≠1:=fun h=>hx (Subtype.ext h)
    have ho:orderOf (x:G)=2:=orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p:=2) (x:G) x.property) hxG
    exact (m.original_two_involution_classes hG x ho).resolve_left hn

theorem normalizerTOrbit_card_ten {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    m.normalizerTOrbit.ncard=10 := by
  have hsub:m.normalizerOrbit⊆Set.univ\{1} := by
    intro x hx
    refine ⟨trivial,?_⟩
    intro he
    have hc:=(m.mem_normalizerOrbit_iff_isConj x).mp hx
    have hx1:(x:G)=1:=congrArg Subtype.val he
    rw [hx1] at hc
    have hz:m.z=1:=by simpa using hc
    have ho:=m.z_order
    rw [hz,orderOf_one] at ho
    omega
  rw [m.normalizerTOrbit_complement hG,Set.ncard_sdiff hsub,
    Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _),Set.ncard_univ,
    m.card_elementaryGroup false false,m.normalizerOrbit_card_five hG]

/-- The two possible local four-point choices remain distinguished. -/
theorem normalizerOrbit_fusion_alternatives {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    (m.fusionFlags 2=true ∧ m.fusionFlags 4=false) ∨
      (m.fusionFlags 2=false ∧ m.fusionFlags 4=true) := by
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
  cases h2:m.fusionFlags 2 <;> cases h4:m.fusionFlags 4 <;> simp_all

end CFSG.Quasithin.Chapter13.Section09.Marking
