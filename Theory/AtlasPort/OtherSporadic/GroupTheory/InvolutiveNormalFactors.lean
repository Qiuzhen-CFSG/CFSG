/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/InvolutiveNormalFactors.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.InvolutiveFactorSwap
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Normal factors exchanged by an involution

An involution-stable normal-subgroup dichotomy splits any proper normal
subgroup into complementary factors. The induced product equivalence
computes the group order from the fixed-point subgroup.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/InvolutiveNormalFactors.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project import.
-/

@[expose] public section

set_option linter.style.haveILetI false

namespace Atlas.GroupTheory

/-- Applying an involutive automorphism twice returns each subgroup. -/
theorem subgroup_map_involution {K : Type*} [Group K] (a : K ≃* K)
    (ha : Function.Involutive a) (N : Subgroup K) :
    (N.map a.toMonoidHom).map a.toMonoidHom = N := by
  ext k
  constructor
  · rintro ⟨y, ⟨x,hx,rfl⟩,rfl⟩
    change a (a x) ∈ N
    rw [ha x]
    exact hx
  · intro hk
    exact ⟨a k, ⟨k,hk,rfl⟩,ha k⟩

/-- In a group with no proper nontrivial normal subgroup invariant under an
involutive automorphism, any proper nontrivial normal subgroup and its image
are complementary normal factors. -/
theorem involutive_normal_factors {K : Type*} [Group K] (a : K ≃* K)
    (ha : Function.Involutive a)
    (hmin : ∀ H : Subgroup K, H.Normal → H.map a.toMonoidHom = H → H = ⊥ ∨ H = ⊤)
    (N : Subgroup K) [N.Normal] (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    N ⊓ N.map a.toMonoidHom = ⊥ ∧ N ⊔ N.map a.toMonoidHom = ⊤ := by
  letI : (N.map a.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance a.toMonoidHom a.surjective
  have hinv : (N ⊓ N.map a.toMonoidHom).map a.toMonoidHom =
      N ⊓ N.map a.toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ a.injective, subgroup_map_involution a ha, inf_comm]
  have hsinv : (N ⊔ N.map a.toMonoidHom).map a.toMonoidHom =
      N ⊔ N.map a.toMonoidHom := by
    rw [Subgroup.map_sup, subgroup_map_involution a ha, sup_comm]
  constructor
  · rcases hmin _ inferInstance hinv with h | h
    · exact h
    · exact False.elim (htop (top_unique (h ▸ inf_le_left)))
  · rcases hmin _ inferInstance hsinv with h | h
    · exact False.elim (hbot (bot_unique (h ▸ le_sup_left)))
    · exact h

/-- Complementary normal factors interchanged by an involution give an actual
product decomposition on which the involution is the coordinate swap. -/
theorem exists_equiv_factorSwap {K : Type*} [Group K] (a : K ≃* K)
    (ha : Function.Involutive a) (N : Subgroup K) [N.Normal]
    (hi : N ⊓ N.map a.toMonoidHom = ⊥)
    (hs : N ⊔ N.map a.toMonoidHom = ⊤) :
    ∃ e : K ≃ N × N, (∀ p, e.symm p = p.1.val * a p.2.val) ∧
      ∀ k, e (a k) = ((e k).2, (e k).1) := by
  let M := N.map a.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance a.toMonoidHom a.surjective
  have hd : Disjoint N M := disjoint_iff.mpr hi
  have hc : N.IsComplement' M := by
    refine ⟨Subgroup.mul_injective_of_disjoint hd, ?_⟩
    intro k
    have hk : k ∈ N ⊔ M := hs.symm ▸ Subgroup.mem_top k
    obtain ⟨n,hn,m,hm,he⟩ := Subgroup.mem_sup_of_normal_right.mp hk
    exact ⟨(⟨n,hn⟩,⟨m,hm⟩),he⟩
  let e : K ≃ N × N := hc.equiv.trans
    (Equiv.prodCongr (Equiv.refl N) (a.subgroupMap N).toEquiv.symm)
  have he (p : N × N) : e.symm p = p.1.val * a p.2.val := rfl
  refine ⟨e, he, ?_⟩
  intro k
  apply e.symm.injective
  rw [e.symm_apply_apply, he]
  have hk : k = (e k).1.val * a (e k).2.val := (e.symm_apply_apply k).symm.trans (he (e k))
  conv_lhs => rw [hk, map_mul, ha]
  exact (Subgroup.commute_of_normal_of_disjoint N M inferInstance inferInstance hd
    (e k).2.val (a (e k).1.val) (e k).2.prop
    ⟨(e k).1.val,(e k).1.prop,rfl⟩).eq.symm

/-- The direct-factor alternative forces the ambient order to be the square
of the involution's fixed-point order. -/
theorem card_eq_sq_fixed_of_normal_factors {K : Type*} [Group K] (a : K ≃* K)
    (ha : Function.Involutive a)
    (hmin : ∀ H : Subgroup K, H.Normal → H.map a.toMonoidHom = H → H = ⊥ ∨ H = ⊤)
    (N : Subgroup K) [N.Normal] (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    Nat.card K = (Nat.card {k : K // a k = k}) ^ 2 := by
  obtain ⟨hi,hs⟩ := involutive_normal_factors a ha hmin N hbot htop
  obtain ⟨e, _, he⟩ := exists_equiv_factorSwap a ha N hi hs
  exact card_eq_sq_fixed_factorSwap e a he

/-- The factor decomposition is an isomorphism of groups, with its inverse
identified as multiplication of a factor and the image of the other factor. -/
theorem exists_mulEquiv_factorSwap {K : Type*} [Group K] (a : K ≃* K)
    (ha : Function.Involutive a) (N : Subgroup K) [N.Normal]
    (hi : N ⊓ N.map a.toMonoidHom = ⊥)
    (hs : N ⊔ N.map a.toMonoidHom = ⊤) :
    ∃ e : K ≃* N × N, (∀ p, e.symm p = p.1.val * a p.2.val) ∧
      ∀ k, e (a k) = ((e k).2, (e k).1) := by
  obtain ⟨e,he,hswap⟩ := exists_equiv_factorSwap a ha N hi hs
  let M := N.map a.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance a.toMonoidHom a.surjective
  have hd : Disjoint N M := disjoint_iff.mpr hi
  let f : N × N ≃* K := {
    e.symm with
    map_mul' := by
      intro p q
      change e.symm (p*q) = e.symm p * e.symm q
      rw [he,he,he]
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
      have hc := (Subgroup.commute_of_normal_of_disjoint N M inferInstance inferInstance hd
        q.1.val (a p.2.val) q.1.prop ⟨p.2.val,p.2.prop,rfl⟩).eq
      simp only [mul_assoc]
      rw [← mul_assoc q.1.val, hc]
      simp only [mul_assoc] }
  exact ⟨f.symm,he,hswap⟩

end Atlas.GroupTheory
