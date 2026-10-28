module
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.SwapFusion

/-!
# The ambient t-class in Q generates the actual B intersection

The four native Q orbits, swap-to-z fusion and t/z nonfusion identify
the ambient t-class in Q as exactly the two indicated local classes.
Three native generators span their actual coordinate subgroup B∩Q.
This retains the original embedding and discharges the Q-fusion input
to the E≤R1 alignment in source 13.9.10.

Source: Aschbacher–Smith 13.9.9–10, printed pp.972–973.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

theorem core_t_fusion_iff {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) (x:G) (hx:x∈m.core) :
    IsConj m.t x ↔ x∈m.coreLocalClass 1 ∨ x∈m.coreLocalClass 3 := by
  have h3:=m.double_transposition_fused_t (hG.evenCharacteristic d.T) (m.centralizer_growth hG).1
  constructor
  · intro hc
    have hx2:orderOf x=2 := by
      obtain ⟨g,hg⟩:=isConj_iff.mp hc
      rw [←hg]
      exact ((MulAut.conj g).orderOf_eq m.t).trans m.t_order
    have hxz:x≠m.z:=by rintro rfl;exact m.not_isConj_t_z hc
    obtain ⟨i,hi,_⟩:=m.local_involution_classes x (d.sylow_le (m.core_le_sylow hx)) hx2
    have hxi:x∈m.coreLocalClass i:=⟨hx,hxz,hi⟩
    have hilocal:=m.isConj_of_mem_localInvolutionClass i x hi
    rcases m.coreLocalClass_indices i x hxi with rfl|rfl|rfl|rfl
    · exact False.elim (m.not_isConj_t_z (hc.trans hilocal.symm))
    · exact Or.inl hxi
    · exact Or.inr hxi
    · exact False.elim (m.not_isConj_t_z (hc.trans ((m.swap_fused_z hG).trans hilocal).symm))
  · rintro (h1|h3x)
    · exact m.isConj_of_mem_localInvolutionClass 1 x h1.2.2
    · exact h3.trans (m.isConj_of_mem_localInvolutionClass 3 x h3x.2.2)

omit [Finite G] in
theorem coreLocalClass_one_three_le_B : m.coreLocalClass 1∪m.coreLocalClass 3⊆m.B := by
  intro x hx
  have hex:∃a:P,(a∈gamma 1 ∨ a∈gamma 3) ∧ m.sylowModelEmbedding a=x := by
    rcases hx with hx|hx
    · rw [m.coreLocalClass_eq_image] at hx
      obtain ⟨a,ha,he⟩:=hx
      exact ⟨a,Or.inl ha,he⟩
    · rw [m.coreLocalClass_eq_image] at hx
      obtain ⟨a,ha,he⟩:=hx
      exact ⟨a,Or.inr ha,he⟩
  obtain ⟨a,ha,rfl⟩:=hex
  have hh:=t_gamma_coordinates a ha
  apply mem_map_of_mem m.embedding
  exact (mem_elementary false false (sylowEmbedding a)).mpr
    ⟨hh.1,⟨a.left 1,hh.2.1,rfl⟩,⟨a.left turn,hh.2.2,rfl⟩⟩

theorem core_t_class_closure {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    Subgroup.closure {x:G | x∈m.core ∧ IsConj m.t x}=m.B⊓m.core := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    exact ⟨m.coreLocalClass_one_three_le_B ((m.core_t_fusion_iff hG x hx.1).mp hx.2),hx.1⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩:=hx.2
    have haB:sylowEmbedding a∈SymmetricFourWreath.B :=
      (mem_map_iff_mem m.embedding_injective).mp hx.1
    have hb:=(mem_elementary false false (sylowEmbedding a)).mp haB
    have ha1:a.left 1∈plane false:=(mem_map_iff_mem square_injective).mp hb.2.1
    have hat:a.left turn∈plane false:=(mem_map_iff_mem square_injective).mp hb.2.2
    obtain ⟨e,he⟩:=t_gamma_span_certificate a ((mem_coreInP a).mp ha) hb.1 ha1 hat
    let H:=Subgroup.closure {x:G | x∈m.core ∧ IsConj m.t x}
    have hgen (i:Fin 3):m.sylowModelEmbedding (tGammaGenerator i)∈H := by
      have hc:m.sylowModelEmbedding (tGammaGenerator i)∈m.coreLocalClass 1 ∨
          m.sylowModelEmbedding (tGammaGenerator i)∈m.coreLocalClass 3 := by
        rcases tGammaGenerator_mem i with hi|hi
        · exact Or.inl ((m.coreLocalClass_eq_image 1).symm ▸ ⟨tGammaGenerator i,hi,rfl⟩)
        · exact Or.inr ((m.coreLocalClass_eq_image 3).symm ▸ ⟨tGammaGenerator i,hi,rfl⟩)
      have hq:m.sylowModelEmbedding (tGammaGenerator i)∈m.core := hc.elim (fun h=>h.1) (fun h=>h.1)
      exact Subgroup.subset_closure ⟨hq,(m.core_t_fusion_iff hG _ hq).mpr hc⟩
    change m.sylowModelEmbedding a∈H
    rw [←he]
    simp only [tGammaWord,map_mul,map_pow]
    exact H.mul_mem (H.mul_mem (H.pow_mem (hgen 0) _) (H.pow_mem (hgen 1) _)) (H.pow_mem (hgen 2) _)

end CFSG.Quasithin.Chapter13.Section09.Marking
