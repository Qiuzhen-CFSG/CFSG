module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.Fitting.TwoCorePreimage
public import Theory.GroupTheory.SolvableSylowOvergroups

/-!
# Rigidity of local components in small Sylow-overgroup models

For local components K ≤ I, intersect I with KT and pass through the literal
quotient I/O₂(I). The intersection contains a Sylow two-subgroup of I. If its
image is proper and every such overgroup is solvable, K would be solvable.
Thus I ≤ KT; both local components then live in the same generated group,
where comparable C-components coincide.

This is the subgroup argument in Aschbacher–Smith 13.1.2(5), printed p.866.
The model-specific hypotheses are discharged by the source consumer.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.LocalModelRigidity
variable {G : Type*} [Group G] [Finite G]

/-- Comparable local components coincide when the upper two-core quotient has
solvable proper Sylow overgroups. No extra normality of the lower component is assumed. -/
theorem local_eq_of_solvableSylowOvergroups {T I K : Subgroup G}
    (hI : I ∈ Chapter1.L G T) (hK : K ∈ Chapter1.L G T) (hKI : K ≤ I)
    (hq : SolvableSylowOvergroups (I ⧸ pCore 2 I)) : K = I := by
  classical
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hI.2.1 (le_sup_left : I ≤ I ⊔ T) hI.1.subnormal
  let P := (I ⊓ (K ⊔ T) : Subgroup G).subgroupOf I
  let q := QuotientGroup.mk' (pCore 2 I)
  let Q := P.map q
  have hSP : (S : Subgroup I) ≤ P := by
    intro s hs
    have hm : (s : G) ∈ T ⊓ I := hS ▸ mem_map_of_mem I.subtype hs
    exact ⟨s.property,mem_sup_right hm.1⟩
  have hcore : pCore 2 I ≤ P := (pCore_isPGroup.le_sylow_of_normal S).trans hSP
  have hQ : Q = ⊤ := by
    by_contra hne
    let Sq := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
    let : Group.IsSolvable Q := hq Sq Q (map_mono hSP) hne
    let f := q.subgroupMap P
    have hk : IsPGroup 2 f.ker := by
      rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    let : Group.IsNilpotent f.ker := hk.isNilpotent
    let : Group.IsSolvable P := Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)
    let e := subgroupOfEquivOfLe (show (I ⊓ (K ⊔ T) : Subgroup G) ≤ I from inf_le_left)
    let : Group.IsSolvable (I ⊓ (K ⊔ T) : Subgroup G) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact Chapter1.mem_L_not_isSolvable hK
      (Group.isSolvable_of_isSolvable_injective
        (inclusion_injective (le_inf hKI (le_sup_left : K ≤ K ⊔ T))))
  have hP : P = ⊤ := by
    have he := congrArg (comap q) hQ
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hcore,comap_top] at he
    exact he
  have hIJ : I ≤ K ⊔ T := by
    intro x hx
    have hm : (⟨x,hx⟩ : I) ∈ P := hP ▸ mem_top _
    exact hm.2
  have he : I ⊔ T = K ⊔ T := le_antisymm (sup_le hIJ le_sup_right) (sup_le_sup_right hKI T)
  have hi : (I.subgroupOf (K ⊔ T)).IsCComponent := he ▸ hI.1
  have hEq := hK.1.eq_of_le hi (comap_mono hKI)
  have hm := congrArg (map (K ⊔ T).subtype) hEq
  simpa only [map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le hIJ] using hm
end CFSG.Quasithin.Chapter13.Section01.LocalModelRigidity
