module

public import Theory.Order.UniqueMaximalOver
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Normalizer bounds from a noncentral normal closure

Suppose Q is normal, normalizes T, and T centralizes Z. If N(Z)Q=G,
every conjugate of T is an N(Z)-conjugate, so its normal closure centralizes
Z. Contrapositively, a noncentral normal closure makes N(Z)Q proper.
When TQ=S and S has a unique maximal overgroup M, this forces N(Z)≤M.

Source: Campbell, *Pushing up in Finite Groups* (1979), II.5.1, printed p.27.
The argument retains the actual subgroups and does not assume a rank-one model.
-/

public section
open scoped Pointwise
namespace Subgroup
theorem closure_centralizes_of_normalizer_supplement {G : Type*} [Group G]
    (T Q Z : Subgroup G) [Q.Normal]
    (hQT : Q ≤ normalizer (T : Set G)) (hTZ : T ≤ centralizer (Z : Set G))
    (hgen : normalizer (Z : Set G) ⊔ Q = ⊤) :
    normalClosure (T : Set G) ≤ centralizer (Z : Set G) := by
  let Y := normalizer (Z : Set G)
  let C := centralizer (Z : Set G)
  let : (C.subgroupOf Y).Normal := normal_subgroupOf_centralizer_normalizer (Z : Set G)
  apply (Subgroup.closure_le (K := centralizer (Z : Set G))).mpr
  intro x hx
  obtain ⟨t,ht,hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g,rfl⟩ := isConj_iff.mp hconj
  have hg : g ∈ Y ⊔ Q := hgen ▸ mem_top g
  obtain ⟨y,hy,q,hq,rfl⟩ := mem_sup_of_normal_right.mp hg
  have ht' : q*t*q⁻¹ ∈ T := (mem_normalizer_iff.mp (hQT hq) t).mp ht
  have htC : q*t*q⁻¹ ∈ C := hTZ ht'
  have htY : q*t*q⁻¹ ∈ Y := Subgroup.centralizer_le_normalizer (Z : Set G) htC
  have hh := (inferInstance : (C.subgroupOf Y).Normal).conj_mem
    (⟨q*t*q⁻¹,htY⟩ : Y) htC (⟨y,hy⟩ : Y)
  change y*(q*t*q⁻¹)*y⁻¹ ∈ C at hh
  change (y*q)*t*(y*q)⁻¹ ∈ C
  simpa only [mul_inv_rev,mul_assoc] using hh

theorem normalizer_le_unique_maximal_of_noncentral_closure {G : Type*} [Group G] [Finite G]
    (S T Q Z M : Subgroup G) [Q.Normal]
    (hu : Order.HasUniqueMaximalOver S ⊤) (hM : S ≤ M ∧ M ⋖ ⊤)
    (hTQ : T ⊔ Q = S) (hQT : Q ≤ normalizer (T : Set G))
    (hTZ : T ≤ centralizer (Z : Set G))
    (hn : ¬ normalClosure (T : Set G) ≤ centralizer (Z : Set G)) :
    normalizer (Z : Set G) ≤ M := by
  have hproper : normalizer (Z : Set G) ⊔ Q < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    exact hn (closure_centralizes_of_normalizer_supplement T Q Z hQT hTZ he)
  have hS : S ≤ normalizer (Z : Set G) ⊔ Q := by
    rw [←hTQ]
    exact sup_le_sup (hTZ.trans (Subgroup.centralizer_le_normalizer _)) le_rfl
  exact le_sup_left.trans (hu.le_maximal hM hS hproper)


end Subgroup
