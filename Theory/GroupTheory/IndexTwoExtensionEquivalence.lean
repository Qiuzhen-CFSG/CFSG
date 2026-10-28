module
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Comparing index-two extensions

Two groups with normal subgroups of index two are isomorphic when an
equivalence of those subgroups matches the square and conjugation action
of a chosen element in each outside coset. The resulting equivalence extends
the given subgroup map and sends the chosen outside elements to each other.
No splitting or finiteness hypothesis is imposed.

Index two gives unique expressions n or n*a. The two normal-form bijections
and the given subgroup equivalence define the candidate ambient equivalence.
Its four multiplication cases use subgroup multiplication, the matched
conjugation action, and the matched square, respectively.

This proves the extension-comparison implication in ABG II.3 Proposition 3,
article pp.26--27. Matching the concrete quotient actions and squares remains
the responsibility of the source-model consumer.
-/

namespace Subgroup

private def pairEval {G : Type*} [Group G] (N : Subgroup G) (a : G) : N × Bool → G :=
  fun x => if x.2 then (x.1 : G) * a else x.1

private theorem pairEval_bijective {G : Type*} [Group G] (N : Subgroup G)
    (hi : N.index = 2) (a : G) (ha : a ∉ N) : Function.Bijective (pairEval N a) := by
  constructor
  · rintro ⟨n, b⟩ ⟨m, c⟩ h
    cases b <;> cases c
    · exact Prod.ext (Subtype.ext h) rfl
    · change (n : G) = (m : G) * a at h
      have hm : (m : G) * a ∈ N := h ▸ n.property
      exact (ha ((N.mul_mem_cancel_left m.property).mp hm)).elim
    · change (n : G) * a = (m : G) at h
      have hn : (n : G) * a ∈ N := h.symm ▸ m.property
      exact (ha ((N.mul_mem_cancel_left n.property).mp hn)).elim
    · change (n : G) * a = (m : G) * a at h
      exact Prod.ext (Subtype.ext (mul_right_cancel h)) rfl
  · intro x
    by_cases hx : x ∈ N
    · exact ⟨(⟨x, hx⟩, false), rfl⟩
    · have hm : x * a⁻¹ ∈ N := by
        rw [N.mul_mem_iff_of_index_two hi, N.inv_mem_iff]
        simp only [hx, ha]
      exact ⟨(⟨x * a⁻¹, hm⟩, true), inv_mul_cancel_right x a⟩

public theorem exists_mulEquiv_of_index_two_extensions
    {G H : Type*} [Group G] [Group H]
    (N : Subgroup G) (N' : Subgroup H) [N.Normal] [N'.Normal]
    (hi : N.index = 2) (hi' : N'.index = 2)
    (a : G) (a' : H) (ha : a ∉ N) (ha' : a' ∉ N')
    (eN : N ≃* N')
    (hsq : (eN ⟨a ^ 2, N.sq_mem_of_index_two hi a⟩ : H) = a' ^ 2)
    (hact : ∀ n : N,
      (eN ⟨a * (n : G) * a⁻¹, (inferInstance : N.Normal).conj_mem n n.property a⟩ : H) =
        a' * (eN n : H) * a'⁻¹) :
    ∃ e : G ≃* H, (∀ n : N, e n = (eN n : H)) ∧ e a = a' := by
  classical
  let e0 : N × Bool ≃ G := Equiv.ofBijective (pairEval N a) (pairEval_bijective N hi a ha)
  let e0' : N' × Bool ≃ H := Equiv.ofBijective (pairEval N' a') (pairEval_bijective N' hi' a' ha')
  let f : G ≃ H := e0.symm.trans ((eN.toEquiv.prodCongr (Equiv.refl Bool)).trans e0')
  have hf (n : N) (b : Bool) : f (pairEval N a (n, b)) = pairEval N' a' (eN n, b) := by
    change e0' ((eN.toEquiv.prodCongr (Equiv.refl Bool)) (e0.symm (e0 (n, b)))) = _
    rw [e0.symm_apply_apply]
    rfl
  have hf0 (n : N) : f (n : G) = (eN n : H) := hf n false
  have hf1 (n : N) : f ((n : G) * a) = (eN n : H) * a' := hf n true
  have hmul (x y : G) : f (x * y) = f x * f y := by
    obtain ⟨⟨n, b⟩, rfl⟩ := (pairEval_bijective N hi a ha).surjective x
    obtain ⟨⟨m, c⟩, rfl⟩ := (pairEval_bijective N hi a ha).surjective y
    cases b <;> cases c
    · change f (((n * m : N) : G)) = f n * f m
      rw [hf0, hf0, hf0, map_mul]
      rfl
    · change f ((n : G) * ((m : G) * a)) = f n * f ((m : G) * a)
      rw [← mul_assoc, show (n : G) * (m : G) = ((n * m : N) : G) from rfl,
        hf1, hf0, hf1, map_mul]
      simp only [coe_mul, mul_assoc]
    · change f (((n : G) * a) * (m : G)) = f ((n : G) * a) * f m
      let t : N := ⟨a * (m : G) * a⁻¹, (inferInstance : N.Normal).conj_mem m m.property a⟩
      have hrew : ((n : G) * a) * (m : G) = ((n * t : N) : G) * a := by
        change (n : G) * a * m = (n : G) * (a * m * a⁻¹) * a
        group
      rw [hrew, hf1, hf1, hf0, map_mul]
      change (eN n : H) * (eN t : H) * a' = ((eN n : H) * a') * eN m
      rw [show (eN t : H) = a' * (eN m : H) * a'⁻¹ from hact m]
      group
    · change f (((n : G) * a) * ((m : G) * a)) = f ((n : G) * a) * f ((m : G) * a)
      let t : N := ⟨a * (m : G) * a⁻¹, (inferInstance : N.Normal).conj_mem m m.property a⟩
      let s : N := ⟨a ^ 2, N.sq_mem_of_index_two hi a⟩
      have hrew : ((n : G) * a) * ((m : G) * a) = ((n * t * s : N) : G) := by
        change (n : G) * a * ((m : G) * a) = (n : G) * (a * m * a⁻¹) * a ^ 2
        group
      rw [hrew, hf0, hf1, hf1, map_mul, map_mul]
      change (eN n : H) * (eN t : H) * (eN s : H) =
        ((eN n : H) * a') * ((eN m : H) * a')
      rw [show (eN t : H) = a' * (eN m : H) * a'⁻¹ from hact m,
        show (eN s : H) = a' ^ 2 from hsq]
      group
  refine ⟨{ f with map_mul' := hmul }, hf0, ?_⟩
  change f a = a'
  have h := hf1 1
  simpa only [coe_one, one_mul, map_one] using h

end Subgroup

