module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormAction
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.PGroup.IndexTwoElementaryConjugate

/-!
# The prescribed Sylow subgroup of a simple norm diagonal

For a simple component moved by an element of a chosen Sylow two-subgroup,
the norm map has trivial kernel. The image of the component's Sylow
intersection is a Sylow subgroup of the norm image and lies in the chosen
ambient Sylow. Maximality identifies the exact intersection. An index-two
component normalizer supplies the two possible conjugate components.

Source: Aschbacher–Smith, E.1.11, printed pp.213–214, paired case.
-/

public section
open Subgroup
namespace Theory.GroupTheory.NormPair
variable {G : Type*} [Group G] {K : Subgroup G} {a : G}

lemma conjugate_eq_or_eq_of_normalizer_index_two
    (hindex : (normalizer (K : Set G)).index = 2)
    (hm : K.map (MulAut.conj a).toMonoidHom ≠ K) (b : G) :
    K.map (MulAut.conj b).toMonoidHom = K ∨
      K.map (MulAut.conj b).toMonoidHom = K.map (MulAut.conj a).toMonoidHom := by
  by_cases hb : b ∈ normalizer (K : Set G)
  · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hb)
  · right
    have ha : a ∉ normalizer (K : Set G) := fun h => hm (mem_normalizer_iff_map_conj_eq.mp h)
    have hn : a⁻¹ * b ∈ normalizer (K : Set G) := by
      rw [(normalizer (K : Set G)).mul_mem_iff_of_index_two hindex,
        (normalizer (K : Set G)).inv_mem_iff]
      exact iff_of_false ha hb
    have hh := congrArg (Subgroup.map (MulAut.conj a).toMonoidHom)
      (mem_normalizer_iff_map_conj_eq.mp hn)
    rw [map_map] at hh
    convert hh using 1
    congr 1
    ext x
    change b * x * b⁻¹ = a * ((a⁻¹ * b) * x * (a⁻¹ * b)⁻¹) * a⁻¹
    group

lemma norm_injective_of_simple (hK : IsComponent G K)
    (hm : K.map (MulAut.conj a).toMonoidHom ≠ K) [IsSimpleGroup K] :
    Function.Injective (componentSwapNorm hK hm) := by
  let := hK.2
  have hz : center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact bot_unique (hz ▸ componentSwapNorm_ker_le_center hK hm)

noncomputable def normEquivOfSimple (hK : IsComponent G K)
    (hm : K.map (MulAut.conj a).toMonoidHom ≠ K) [IsSimpleGroup K] :
    K ≃* normRange hK hm := MonoidHom.ofInjective (norm_injective_of_simple hK hm)

lemma exists_sylow_intersection [Finite G] (T : Sylow 2 G)
    (hK : IsComponent G K) (hm : K.map (MulAut.conj a).toMonoidHom ≠ K)
    [IsSimpleGroup K] (ha : a ∈ (T : Subgroup G)) :
    ∃ S : Sylow 2 (normRange hK hm),
      (S : Subgroup (normRange hK hm)) = (T : Subgroup G).subgroupOf (normRange hK hm) := by
  obtain ⟨R,hR⟩ := T.exists_subgroupOf_eq_of_subnormal K hK.1
  let e := normEquivOfSimple hK hm
  let S := R.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨S, ?_⟩
  symm
  apply S.is_maximal' (T.isPGroup'.comap_of_injective _ (normRange hK hm).subtype_injective)
  rintro x ⟨r,hr,rfl⟩
  have hrT : (r : G) ∈ (T : Subgroup G) := by
    rw [hR] at hr
    exact hr
  change (r : G) * (a * r * a⁻¹) ∈ (T : Subgroup G)
  exact mul_mem hrT (mul_mem (mul_mem ha hrT) (inv_mem ha))

end Theory.GroupTheory.NormPair
