module
public import Theory.GroupTheory.NormalizerAction
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Commutators in a normalizer with cyclic Sylow action

Conjugacy of Sylow subgroups transports cyclicity of one action image to every
p-subgroup. For a normalizer action this puts the derived subgroup in the
centralizer. The literal normalizer and action map are retained for the TI
fusion argument in Aschbacher–Smith, 2.4.21, printed p.536.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite G]

theorem isCyclic_map_of_sylow_map {p : ℕ} [Fact p.Prime]
    (f : G →* H) (P : Sylow p G) [IsCyclic ((P : Subgroup G).map f)]
    (I : Subgroup G) (hI : IsPGroup p I) : IsCyclic (I.map f) := by
  obtain ⟨Q,hIQ⟩ := hI.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P Q
  have hm : (Q : Subgroup G).map f =
      ((P : Subgroup G).map f).map (MulAut.conj (f g)).toMonoidHom := by
    rw [←hg]
    change ((P : Subgroup G).map (MulAut.conj g).toMonoidHom).map f = _
    rw [map_map,map_map]
    congr 1
    ext x
    change f (g*x*g⁻¹)=f g*f x*(f g)⁻¹
    simp only [map_mul,map_inv]
  let e := (MulAut.conj (f g)).toMonoidHom
  let : IsCyclic ((Q : Subgroup G).map f) := by
    rw [hm]
    exact isCyclic_of_surjective (e.subgroupMap ((P : Subgroup G).map f))
      (e.subgroupMap_surjective _)
  exact isCyclic_of_le (map_mono hIQ)
theorem normalizer_commutator_le_centralizer_of_sylow_action
    (Z : Subgroup G) (P : Sylow 2 G) (hP : (P : Subgroup G) ≤ normalizer (Z : Set G))
    (hc : IsCyclic ((Z.normalizerMonoidHom.comp (inclusion hP)).range))
    (I : Subgroup G) (hI : IsPGroup 2 I) (hIN : I ≤ normalizer (Z : Set G)) :
    ⁅I,I⁆ ≤ centralizer (Z : Set G) := by
  let N := normalizer (Z : Set G)
  let ρ := Z.normalizerMonoidHom
  let Q := P.subtype hP
  have hQ : (Q : Subgroup N).map ρ = (ρ.comp (inclusion hP)).range := by
    rw [MonoidHom.range_comp,inclusion_range]
    rfl
  let : IsCyclic ((Q : Subgroup N).map ρ) := hQ.symm ▸ hc
  let J := I.subgroupOf N
  let : IsCyclic (J.map ρ) := isCyclic_map_of_sylow_map ρ Q J
    (hI.of_injective (subgroupOfEquivOfLe hIN).toMonoidHom (subgroupOfEquivOfLe hIN).injective)
  have hj : (⁅J,J⁆).map ρ = ⊥ := by
    rw [map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hk : ⁅J,J⁆ ≤ ρ.ker := map_le_iff_le_comap.mp hj.le
  have hmap : J.map N.subtype = I := map_subgroupOf_eq_of_le hIN
  rw [←hmap,←map_commutator]
  apply map_le_iff_le_comap.mpr
  exact hk.trans_eq (normalizerMonoidHom_ker Z)
end Theory.GroupTheory

