module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Automorphism
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Normalizer
public import Theory.GroupTheory.SemidihedralSixteenPair
/-! The certified outer actor and core involution give an actual semidihedral
Sylow subgroup of the fixed full-Ree max4 normalizer. The intrinsic order
15600 follows from its 7800 core, the order-16 pair, and native five-overgroup
coverage. Source: Aschbacher–Smith J.5.4, printed pp.445–446. -/

@[expose] public section
open Subgroup
noncomputable section
namespace Tits.Max4Outer
open MinimumIndexCandidates ExceptionalParabolics.FullRee
open ExceptionalParabolics.FullRee.FiveOvergroups

def element : ReeF4.Model 0 := atlasAutEquiv.symm automorphism

theorem element_action : atlasAction element=automorphism := by
  change atlasAutEquiv (atlasAutEquiv.symm automorphism)=automorphism
  exact atlasAutEquiv.apply_symm_apply _

theorem element_square : element^2=atlasEmbedding squareElement := by
  apply atlasAutEquiv.injective
  rw [map_pow,atlasAutEquiv_embedding]
  change (atlasAutEquiv (atlasAutEquiv.symm automorphism))^2=_
  rw [MulEquiv.apply_symm_apply,automorphism_square]

theorem element_mem : element∈candidateNormalizer := by
  rw [candidateNormalizer,mem_normalizer_iff_map_conj_eq,candidate,map_map]
  have hc : (MulAut.conj element).toMonoidHom.comp atlasEmbedding =
      atlasEmbedding.comp automorphism.toMonoidHom := by
    ext x : 1
    change element*atlasEmbedding x*element⁻¹=atlasEmbedding (automorphism x)
    rw [← element_action]
    exact (atlasAction_apply element x).symm
  change max4.map ((MulAut.conj element).toMonoidHom.comp atlasEmbedding)=_
  rw [hc,← map_map,automorphism_preserves]

theorem reflection_mem : atlasEmbedding reflection∈candidateNormalizer :=
  candidate.le_normalizer (mem_map_of_mem atlasEmbedding (eval_core_mem reflectionWord))

def rotation : candidateNormalizer := ⟨element,element_mem⟩
def reflector : candidateNormalizer := ⟨atlasEmbedding reflection,reflection_mem⟩

theorem rotation_order : orderOf rotation=8 := by
  rw [← orderOf_coe]
  change orderOf (atlasAutEquiv.symm automorphism)=8
  exact (orderOf_injective atlasAutEquiv.symm.toMonoidHom atlasAutEquiv.symm.injective _).trans automorphism_order

theorem reflector_order : orderOf reflector=2 := by
  rw [← orderOf_coe]
  change orderOf (atlasEmbedding reflection)=2
  rw [orderOf_injective _ atlasEmbedding_injective,reflection_order]

theorem rotation_conjugate : reflector*rotation*reflector⁻¹=rotation^3 := by
  apply Subtype.ext
  apply atlasAutEquiv.injective
  change atlasAutEquiv (atlasEmbedding reflection*element*(atlasEmbedding reflection)⁻¹)=
    atlasAutEquiv (element^3)
  simp only [map_mul,map_inv,map_pow,atlasAutEquiv_embedding]
  change MulAut.conj reflection*atlasAutEquiv (atlasAutEquiv.symm automorphism)*
    (MulAut.conj reflection)⁻¹=(atlasAutEquiv (atlasAutEquiv.symm automorphism))^3
  simpa only [MulEquiv.apply_symm_apply] using semidihedral_relation

def sixteen : Subgroup candidateNormalizer := zpowers rotation ⊔ zpowers reflector

theorem sixteen_spec : Nat.card sixteen=16 ∧ Stellmacher.IsSemidihedralGroup sixteen :=
  Semidihedral.sixteen_of_pair rotation reflector rotation_order reflector_order rotation_conjugate

theorem candidate_card : Nat.card candidate=7800 := by
  rw [candidate,card_map_of_injective atlasEmbedding_injective,Max4Projective.max4_card]

theorem candidate_comap : candidate.comap atlasEmbedding=max4 := by
  ext x
  constructor
  · rintro ⟨y,hy,he⟩
    exact atlasEmbedding_injective he ▸ hy
  · intro hx
    exact mem_map_of_mem atlasEmbedding hx

theorem derived_not_le_normalizer : ¬ D≤candidateNormalizer := by
  intro hd
  have hn : normalizer (max4 : Set Atlas1600Group)=⊤ := by
    have he := comap_normalizer_eq_of_le_range (H := candidate)
      (show candidate ≤ atlasEmbedding.range from map_le_range atlasEmbedding max4)
    rw [← candidate_comap,← he]
    apply top_unique
    intro x _
    exact hd (by
      change atlasEmbedding x ∈ commutator (ReeF4.Model 0)
      rw [← atlasEmbedding_range]
      exact ⟨x,rfl⟩)
  have hm : max4.Normal := normalizer_eq_top_iff.mp hn
  rcases hm.eq_bot_or_eq_top with he|he
  · have hh := Max4Projective.max4_card
    rw [he,card_bot] at hh
    norm_num at hh
  · have hh := Max4Projective.max4_card
    rw [he,card_top,atlas1600Group_card] at hh
    norm_num at hh

theorem normalizer_card : Nat.card candidateNormalizer=15600 := by
  have hc : 7800∣Nat.card candidateNormalizer :=
    candidate_card ▸ card_dvd_of_le candidate.le_normalizer
  have h16 : 16∣Nat.card candidateNormalizer :=
    sixteen_spec.1 ▸ sixteen.card_subgroup_dvd_card
  have hd : 15600∣Nat.card candidateNormalizer := by
    have h := Nat.lcm_dvd hc h16
    norm_num at h
    exact h
  apply Nat.le_antisymm
  · exact FiveOvergroups.card_le candidateNormalizer derived_not_le_normalizer
      (dvd_trans (by norm_num : 25∣7800) hc)
  · exact Nat.le_of_dvd Nat.card_pos hd

def sylow : Sylow 2 candidateNormalizer := Sylow.ofCard sixteen (by
  rw [sixteen_spec.1,normalizer_card]
  decide +kernel)

theorem sylow_coe : (sylow : Subgroup candidateNormalizer)=sixteen := Sylow.coe_ofCard _ _

theorem sylow_semidihedral : Stellmacher.IsSemidihedralGroup sylow := by
  rw [sylow_coe]
  exact sixteen_spec.2

end Tits.Max4Outer
