module

public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Elementary automorphism rank and the fixed inner kernel

For a centerless finite group, the inner actors in an elementary abelian
automorphism group are implemented uniquely by group elements. Commutation
with a chosen actor places those elements in its actual fixed subgroup.
The kernel-image rank inequality then bounds the elementary group's rank by
the fixed-subgroup rank plus the rank of its actual image in Aut/Inn.

This applies to elementary subgroups of the standard PSL₃ automorphisms
without assuming that standard automorphisms exhaust the full group.
It does not supply either of the model-specific rank calculations.

Source application: Aschbacher–Smith, the automorphism-rank inspection in
16.3.9, printed p.1180; compare G.9, printed p.356.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conj_fixed_of_commute (hc : center G = ⊥)
    (a : MulAut G) (g : G) (h : MulAut.conj g * a = a * MulAut.conj g) :
    a g = g := by
  apply MulAut.conj_injective_of_center_eq_bot hc
  have he : MulAut.conj (a g) = a * MulAut.conj g * a⁻¹ := by
    ext x
    simp
  rw [he, ← h, mul_inv_cancel_right]

private theorem elementary_kernel_rank (hc : center G = ⊥)
    (E : Subgroup (MulAut G)) [IsElementaryAbelian 2 E]
    (a : MulAut G) (ha : a ∈ E) :
    primeRank 2 ((QuotientGroup.mk' (MulAut.innerSubgroup G)).comp E.subtype).ker ≤
      primeRank 2 a.fixedSubgroup := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup G)
  let f := q.comp E.subtype
  let e : G ≃* MulAut.innerSubgroup G :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hc)
  let k : f.ker →* MulAut.innerSubgroup G :=
    { toFun := fun x => ⟨x.1.1, (QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g := e.symm.toMonoidHom.comp k
  have hg (x : f.ker) : MulAut.conj (g x) = x.1.1 := by
    exact congrArg Subtype.val (e.apply_symm_apply (k x))
  have hfixed (x : f.ker) : g x ∈ a.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply conj_fixed_of_commute hc
    rw [hg]
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm x.1 (⟨a, ha⟩ : E))
  let j : f.ker →* a.fixedSubgroup := g.codRestrict _ hfixed
  apply primeRank_le_of_injective 2 j
  intro x y hxy
  have h := congrArg (fun z : a.fixedSubgroup => MulAut.conj (z : G)) hxy
  change MulAut.conj (g x) = MulAut.conj (g y) at h
  rw [hg, hg] at h
  exact Subtype.ext (Subtype.ext h)

/-- An elementary group of actual automorphisms has rank at most the rank
of the fixed subgroup of any one of its actors plus the rank of its outer image. -/
theorem elementary_automorphism_two_rank_le (hc : center G = ⊥)
    (E : Subgroup (MulAut G)) [IsElementaryAbelian 2 E]
    (a : MulAut G) (ha : a ∈ E) :
    primeRank 2 E ≤ primeRank 2 a.fixedSubgroup +
      primeRank 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup G))) := by
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup G)).comp E.subtype
  have h := primeRank_le_ker_add (p := 2) f.rangeRestrict
  rw [MonoidHom.ker_rangeRestrict] at h
  have hk := elementary_kernel_rank hc E a ha
  have hr := h.trans (Nat.add_le_add_right hk (primeRank 2 f.range))
  have he : f.range = E.map (QuotientGroup.mk' (MulAut.innerSubgroup G)) := by
    exact MonoidHom.range_comp _ _ |>.trans (congrArg (Subgroup.map _) E.range_subtype)
  rwa [he] at hr

end Theory.GroupTheory
