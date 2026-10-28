module
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.PGroup
public import Theory.ElementaryAbelian.Basic

/-!
# Elementwise fusion bounds in a normal subgroup

A fusion bound in a chosen Sylow subgroup extends to its overgroup when
the target subgroup is normal there: conjugate the cyclic two-subgroup
into the chosen Sylow and transport back. Applied generator by generator,
this also places an element-generated subgroup in a conjugate target
after conjugating its ambient centralizer into the overgroup.

Source application: Aschbacher–Smith, 2.4.21, printed p.536.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow fusion bound extends to a normal subgroup of its overgroup. -/
theorem fused_element_mem_of_sylow_bound
    (T : Sylow 2 G) (M R : Subgroup G) (hTM : (T : Subgroup G)≤M)
    (hMR : M≤normalizer (R : Set G)) (z : G) (hz2 : z^2=1)
    (hbound : ∀ t∈T, IsConj t z → t∈R)
    (a : G) (haM : a∈M) (hfused : IsConj a z) : a∈R := by
  have ha2 : a^2=1 := isConj_one_left.mp (by simpa only [hz2] using IsConj.pow 2 hfused)
  let A := zpowers a
  have hp : IsPGroup 2 A := (IsElementaryAbelian.zpowers_of_pow_eq_one ha2).isPGroup
  have hAM : A≤M := zpowers_le.mpr haM
  obtain ⟨P,hAP⟩ := (hp.comap_subtype (K:=M)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M P (T.subtype hTM)
  have hgaT : (g:G)*a*(g:G)⁻¹∈T := by
    have hh : (MulAut.conj g) ⟨a,haM⟩∈(T.subtype hTM : Subgroup M) := by
      rw [←hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hAP (mem_zpowers a))
    exact hh
  have hgaR := hbound _ hgaT ((isConj_iff.mpr ⟨(g:G),rfl⟩).symm.trans hfused)
  exact (mem_normalizer_iff.mp (hMR g.property) a).mpr hgaR

/-- Elementwise fusion generation enters a conjugate normal subgroup after centralizer transport. -/
theorem fused_generated_subgroup_le_conjugate
    (T : Sylow 2 G) (M R : Subgroup G) (hTM : (T : Subgroup G)≤M)
    (hMR : M≤normalizer (R : Set G)) (z : G) (hz2 : z^2=1)
    (hbound : ∀ t∈T, IsConj t z → t∈R)
    (u a g : G) (ha : a=g*u*g⁻¹)
    (hCM : centralizer ({u} : Set G)≤M)
    (I : Subgroup G) (hI : I≤centralizer ({a} : Set G))
    (hgen : closure {v | v∈I ∧ IsConj z v}=I) : I≤R.conjBy g := by
  rw [←hgen]
  apply (closure_le _).mpr
  rintro v ⟨hv,hzv⟩
  let w := (MulAut.conj g⁻¹) v
  have ha' : (MulAut.conj g⁻¹) a=u := by
    rw [ha]
    simp only [MulAut.conj_apply,inv_inv]
    group
  have hwM : w∈M := by
    apply hCM
    rw [mem_centralizer_singleton_iff]
    have hm := (show Commute v a from mem_centralizer_singleton_iff.mp (hI hv)).map
      (MulAut.conj g⁻¹).toMonoidHom
    change w * (MulAut.conj g⁻¹) a = (MulAut.conj g⁻¹) a * w at hm
    rwa [ha'] at hm
  have hwz : IsConj w z := (hzv.trans (isConj_iff.mpr ⟨g⁻¹,rfl⟩)).symm
  have hwR := fused_element_mem_of_sylow_bound T M R hTM hMR z hz2 hbound w hwM hwz
  refine ⟨w,hwR,?_⟩
  change g*(g⁻¹*v*(g⁻¹)⁻¹)*g⁻¹=v
  group
end Subgroup
