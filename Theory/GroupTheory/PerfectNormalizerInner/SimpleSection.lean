module
public import Theory.GroupTheory.PerfectNormalizerInner
public import Theory.GroupTheory.PerfectSimpleImage

/-!
# Inner action from exclusion of the actual simple section

A perfect actor with a simple quotient and solvable kernel has trivial
outer image whenever the component's outer group has no such simple section.
The implementing element lies in the literal component. This is weaker than
requiring the full outer group to be solvable.

Source: the unitary G2(2)' specialization of Aschbacher--Smith 4.4.10,
printed p.621.
-/
public section
open Subgroup
namespace Subgroup
variable {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]

/-- The actual simple-section exclusion suffices for inner placement. -/
theorem perfect_le_sup_centralizer_of_no_simple_outer_section (K F : Subgroup G)
    [Group.IsPerfect F] (q:F→*S) (hq:Function.Surjective q) [Group.IsSolvable q.ker]
    (hno:∀U:Subgroup (MulAut.Outer K),∀g:U→*S,¬Function.Surjective g)
    (hF:F≤normalizer (K:Set G)) : F≤K⊔centralizer (K:Set G) := by
  let a : F →* MulAut K := K.normalizerMonoidHom.comp (inclusion hF)
  let f : F →* MulAut.Outer K := (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp a
  have hone:f=1:=Theory.GroupTheory.hom_eq_one_of_no_simple_section q hq hno f
  intro x hx
  have hf : f ⟨x,hx⟩ = 1 := DFunLike.congr_fun hone ⟨x,hx⟩
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

end Subgroup
