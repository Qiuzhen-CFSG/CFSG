module
public import Theory.Representation.BinaryTensorThree.ParabolicRadicals
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Hyperplanes from the marked tensor-radical action

A binary translation character has an index-two kernel. Its kernel fixes the
translated vector, so the prescribed translation belongs to the commutator
of the kernel's fixed subgroup with the original actor. We apply this to
the two actual parabolic radicals of the binary three-by-three tensor.

All subgroups and conjugations are in the original ambient group. The tensor
coordinates are an equivariant linear equivalence, and the actor map may have
the genuine action kernel. The Chapter 10 quiet-module consumer uses this
result to discharge the hyperplane premise of 8.3.14.
Source: Aschbacher--Smith, proof of 8.3.14, printed p.727.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

/-- A nonzero binary translation character produces an actual index-two
subgroup whose centralizer commutator contains the prescribed point. -/
theorem hyperplane_of_binary_translation
    (V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hAN : A ≤ normalizer (V : Set G)) (w z : Additive V)
    (χ : A →* Multiplicative (ZMod 2)) (hχ : Function.Surjective χ)
    (hline : ∀ a : A,
      Additive.ofMul (V.normalizerMonoidHom ⟨a,hAN a.property⟩ w.toMul) =
        w + (χ a).toAdd • z) :
    ∃ B : Subgroup G, B ≤ A ∧ B.relIndex A = 2 ∧
      (z.toMul : G) ∈ ⁅V ⊓ centralizer (B : Set G),A⁆ := by
  let B := χ.ker.map A.subtype
  have hindex : B.relIndex A = 2 := by
    have hm : (⊤ : Subgroup A).map A.subtype = A := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    rw [← hm, relIndex_map_map_of_injective _ _ A.subtype_injective,
      relIndex_top_right, index_ker, MonoidHom.range_eq_top.mpr hχ, card_top]
    exact Nat.card_zmod 2
  have hwB : (w.toMul : G) ∈ centralizer (B : Set G) := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := hb
    have hzero : (χ a).toAdd = 0 := congrArg Multiplicative.toAdd ha
    have he := hline a
    rw [hzero,zero_smul,add_zero] at he
    have he' := congrArg (fun u : Additive V => (u.toMul : G)) he
    change (a : G) * (w.toMul : G) * (a : G)⁻¹ = (w.toMul : G) at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  obtain ⟨a,ha⟩ := hχ (Multiplicative.ofAdd 1)
  have he := hline a
  rw [ha] at he
  change Additive.ofMul (V.normalizerMonoidHom ⟨a,hAN a.property⟩ w.toMul) =
    w + (1 : ZMod 2) • z at he
  rw [one_smul] at he
  have he' : (a : G) * (w.toMul : G) * (a : G)⁻¹ =
      (w.toMul : G) * (z.toMul : G) := by
    exact congrArg (fun u : Additive V => (u.toMul : G)) he
  have hc : ⁅(a : G),(w.toMul : G)⁆ = (z.toMul : G) := by
    rw [commutatorElement_def,he']
    have hzcomm : (w.toMul : G) * (z.toMul : G) = (z.toMul : G) * (w.toMul : G) :=
      congrArg Subtype.val (mul_comm w.toMul z.toMul)
    rw [hzcomm,mul_inv_cancel_right]
  refine ⟨B,map_subtype_le _,hindex,?_⟩
  rw [←hc,commutator_comm]
  exact commutator_mem_commutator a.property ⟨w.toMul.property,hwB⟩

open BinaryTensorThree

/-- Transport the literal tensor-radical calculation to the original ambient
subgroups. The marked point itself lies in the resulting commutator. -/
theorem tensor_hyperplane_of_radical_coordinates
    (V S : Subgroup G) [IsElementaryAbelian 2 V]
    (hSN : S ≤ normalizer (V : Set G))
    (q : S →* Radical × Radical)
    (e : Additive V ≃ₗ[ZMod 2] Space)
    (he : ∀ (s : S) (v : Additive V),
      e (Additive.ofMul (V.normalizerMonoidHom ⟨s,hSN s.property⟩ v.toMul)) =
        action (radicalPair (q s)) (e v))
    {z : G} (hzV : z ∈ V) (hez : e (Additive.ofMul ⟨z,hzV⟩) = point)
    {A : Subgroup G} (hAS : A ≤ S) (hmove : ¬ A ≤ centralizer (V : Set G)) :
    ∃ B : Subgroup G, B ≤ A ∧ B.relIndex A = 2 ∧
      z ∈ ⁅V ⊓ centralizer (B : Set G),A⁆ := by
  let qA := q.comp (inclusion hAS)
  have hqA : ∃ a : A, qA a ≠ 1 := by
    by_contra h
    push Not at h
    apply hmove
    intro a ha
    apply mem_centralizer_iff.mpr
    intro v hv
    have hh := he (inclusion hAS ⟨a,ha⟩) (Additive.ofMul ⟨v,hv⟩)
    change e (Additive.ofMul (V.normalizerMonoidHom ⟨a,hSN (hAS ha)⟩ ⟨v,hv⟩)) =
      action (radicalPair (qA ⟨a,ha⟩)) (e (Additive.ofMul ⟨v,hv⟩)) at hh
    rw [h, map_one, map_one] at hh
    have hh' := congrArg (fun u : Additive V => (u.toMul : G)) (e.injective hh)
    change a * v * a⁻¹ = v at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  obtain ⟨χ,w,hχ,hline⟩ := exists_binary_translation qA hqA
  apply hyperplane_of_binary_translation V A (hAS.trans hSN)
    (e.symm w) (Additive.ofMul ⟨z,hzV⟩) χ hχ
  intro a
  apply e.injective
  rw [map_add,map_smul,hez,LinearEquiv.apply_symm_apply]
  have hh := he (inclusion hAS a) (e.symm w)
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.trans (hline a)


end Subgroup
