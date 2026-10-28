module
public import Theory.SpecificGroups.SL2.SubgroupTwoCore
public import Theory.GroupTheory.PRadical.NormalizerRestriction
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# Binary rank-one radical subgroups and their local lifts

A nonidentity two-subgroup of binary SL₂ has its normalizer in the Borel
of a containing Sylow subgroup. Radical saturation therefore makes every
nontrivial two-radical subgroup Sylow. In a two-kernel cover, a radical is
either the kernel or a full Sylow subgroup. The final form applies inside
an ambient overgroup normalized by the original radical normalizer.

Source: Aschbacher (1981), 8.2(7), the rank-one quotient step for the
symplectic parabolics used in Aschbacher–Smith C.2.7, pp.146–147.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem radical_eq_sylow (U : Subgroup SL(2,F)) (hU : U.IsPRadical 2) :
    ∃ S : Sylow 2 SL(2,F), (S : Subgroup _) = U := by
  obtain ⟨S,hUS⟩ := hU.isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) S (upperUnipotentSylow F 2)
  let e := MulAut.conj g
  have hm : (S : Subgroup SL(2,F)).map e.toMonoidHom = upperUnipotent F :=
    congrArg Sylow.toSubgroup hg
  have hr := hU.map_equiv e
  have hn := normalizer_le_rankOneBorel_of_le_upperUnipotent
    (U.map e.toMonoidHom) (hm ▸ map_mono hUS) hr.1
  have hle := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    (U.map e.toMonoidHom) (upperUnipotent F)
    hr.isPGroup (upperUnipotentSylow F 2).isPGroup' hr.2.le hn
  refine ⟨S,?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [hm]
  exact le_antisymm hle (hm ▸ map_mono hUS)

variable {G : Type*} [Group G] [Finite G]

theorem radical_local_eq_kernel_or_sylow
    (R L : Subgroup G) (hR : R.IsPRadical 2) (hRL : R ≤ L)
    (hn : normalizer (R : Set G) ≤ normalizer (L : Set G))
    (q : L →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ L) :
    R = q.ker.map L.subtype ∨ ∃ S : Sylow 2 G, (S : Subgroup G) = R := by
  let U := R.subgroupOf L
  have hc := hR.normalizer_core_subgroupOf L hRL hn
  have hkU : q.ker ≤ U := (le_sSup ⟨inferInstance,hk⟩ : q.ker ≤ pCore 2 L).trans
    (pCore_le_of_pCore_normalizer_le U hR.isPGroup.comap_subtype hc.le)
  by_cases hz : U.map q = ⊥
  · left
    have he : U = q.ker := le_antisymm ((map_eq_bot_iff U).mp hz) hkU
    have hh := congrArg (Subgroup.map L.subtype) he
    rwa [map_subgroupOf_eq_of_le hRL] at hh
  · have hr : (U.map q).IsPRadical 2 := ⟨hz,
      map_normalizer_core_of_p_kernel U hR.isPGroup.comap_subtype hc q hq hkU⟩
    obtain ⟨S,hS⟩ := radical_eq_sylow (U.map q) hr
    let S' := S.comapOfKerIsPGroup q hk
      (by rw [MonoidHom.range_eq_top_of_surjective _ hq]; exact le_top)
    have he : (S' : Subgroup L) = U := by
      change (S : Subgroup SL(2,F)).comap q = U
      rw [hS,comap_map_eq_self hkU]
    have hindex : ¬2 ∣ R.index := by
      have hh : ((S' : Subgroup L).map L.subtype) = R := by
        rw [he,map_subgroupOf_eq_of_le hRL]
      rw [←hh,index_map_subtype]
      exact Nat.prime_two.not_dvd_mul S'.not_dvd_index
        (fun hd => T.not_dvd_index (hd.trans (index_dvd_of_le hTL)))
    exact Or.inr ⟨hR.isPGroup.toSylow hindex,rfl⟩
end Matrix.SpecialLinearGroup
