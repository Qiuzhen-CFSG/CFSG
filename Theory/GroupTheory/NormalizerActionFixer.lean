module
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Sylow
/-! # Pointwise-fixer preimages in a subgroup normalizer action
The preimage of a pointwise fixer is the literal ambient centralizer.
A two-group fixer and two-group action kernel give a two-group centralizer;
if the chosen Sylow subgroup normalizes it, maximality puts it in that Sylow.
This is the local action step of Aschbacher--Smith 2.5.15, p.559.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G]

theorem normalizer_action_fixing_comap (K H : Subgroup G) (R : Subgroup K)
    (hHN : H ≤ normalizer (K : Set G)) :
    (fixingSubgroup (MulAut K) (R : Set K)).comap
      (K.normalizerMonoidHom.comp (inclusion hHN)) =
      (centralizer (R.map K.subtype : Set G)).subgroupOf H := by
  ext h
  rw [mem_comap,mem_fixingSubgroup_iff]
  constructor
  · intro hf r hr
    obtain ⟨r,hr,rfl⟩ := hr
    have hh := congrArg Subtype.val (hf r hr)
    change (h : G) * (r : G) * (h : G)⁻¹ = (r : G) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hc r hr
    apply Subtype.ext
    change (h : G) * (r : G) * (h : G)⁻¹ = (r : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hc r (mem_map_of_mem K.subtype hr)).symm

theorem normalizer_action_ker_comap (K H : Subgroup G)
    (hHN : H ≤ normalizer (K : Set G)) :
    (K.normalizerMonoidHom.comp (inclusion hHN)).ker =
      (centralizer (K : Set G)).subgroupOf H := by
  ext h
  change K.normalizerMonoidHom (inclusion hHN h) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

theorem normalizer_action_fixer_le_sylow (K H : Subgroup G) (R : Subgroup K)
    (hHN : H ≤ normalizer (K : Set G)) (S : Sylow 2 H)
    (hker : H ⊓ centralizer (K : Set G) ≤ (S : Subgroup H).map H.subtype)
    (hfix : IsPGroup 2 (fixingSubgroup (MulAut K) (R : Set K)))
    (hSN : (S : Subgroup H).map H.subtype ≤ normalizer (R.map K.subtype : Set G)) :
    H ⊓ centralizer (R.map K.subtype : Set G) ≤ (S : Subgroup H).map H.subtype := by
  let α := K.normalizerMonoidHom.comp (inclusion hHN)
  let C := (centralizer (R.map K.subtype : Set G)).subgroupOf H
  have hk : IsPGroup 2 α.ker := by
    apply S.isPGroup'.to_le
    intro h hh
    rw [normalizer_action_ker_comap] at hh
    have hm := hker ⟨h.property,hh⟩
    obtain ⟨s,hs,he⟩ := hm
    exact (H.subtype_injective he) ▸ hs
  have hc : IsPGroup 2 C := by
    change IsPGroup 2 ((centralizer (R.map K.subtype : Set G)).subgroupOf H)
    rw [← normalizer_action_fixing_comap K H R hHN]
    exact hfix.comap_of_ker_isPGroup α hk
  have hn : (S : Subgroup H) ≤ normalizer (C : Set H) := by
    intro s hs
    apply le_normalizer_comap H.subtype
    exact normalizer_le_normalizer_centralizer (R.map K.subtype)
      (hSN (mem_map_of_mem H.subtype hs))
  have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' hc hn) le_sup_left
  have hCS : C ≤ S := by rw [← he]; exact le_sup_right
  intro x hx
  exact mem_map_of_mem H.subtype (hCS (show (⟨x,hx.1⟩ : H) ∈ C from hx.2))
end Subgroup
