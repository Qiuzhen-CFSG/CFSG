module
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-! Perfect normalizing actors have trivial image in a solvable outer group.
The implementing element belongs to the original subgroup, so the conclusion
uses its literal ambient centralizer and retains any central covering kernel.
This is the elementary action step in Aschbacher–Smith 4.4.3, printed p.621. -/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem perfect_le_sup_centralizer_of_solvable_outer (K F : Subgroup G)
    [Group.IsPerfect F] [Group.IsSolvable (MulAut.Outer K)]
    (hF : F ≤ normalizer (K : Set G)) : F ≤ K ⊔ centralizer (K : Set G) := by
  let a : F →* MulAut K := K.normalizerMonoidHom.comp (inclusion hF)
  let f : F →* MulAut.Outer K := (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp a
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro x hx
  have hf : f ⟨x,hx⟩ = 1 := congrArg f.range.subtype
    (hs.elim (⟨f ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩⟩ : f.range) 1)
  obtain ⟨k,hk⟩ := (QuotientGroup.eq_one_iff _).mp hf
  let kN : normalizer (K : Set G) := ⟨k,K.le_normalizer k.property⟩
  have hkN : K.normalizerMonoidHom kN = MulAut.conj k := by ext y; rfl
  have hker : kN⁻¹ * ⟨x,hF hx⟩ ∈ K.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,hkN,hk]
    exact inv_mul_cancel _
  rw [normalizerMonoidHom_ker] at hker
  have hm := (K ⊔ centralizer (K : Set G)).mul_mem
    (mem_sup_left k.property)
    (mem_sup_right (show (k : G)⁻¹ * x ∈ centralizer (K : Set G) from hker))
  simpa only [mul_inv_cancel_left] using hm

theorem perfect_le_sup_centralizer_of_solvable_central_outer (K F : Subgroup G)
    [Group.IsPerfect K] [Group.IsPerfect F]
    [Group.IsSolvable (MulAut.Outer (K ⧸ center K))]
    (hF : F ≤ normalizer (K : Set G)) : F ≤ K ⊔ centralizer (K : Set G) := by
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  exact perfect_le_sup_centralizer_of_solvable_outer K F hF
end Subgroup
