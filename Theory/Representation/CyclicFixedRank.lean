module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Abel

/-!
# Cyclic commutators and inverted cubic fixed ranks

Cyclic commutators form the image of the generator minus the identity.
In finite dimension, generation by these commutators therefore excludes
fixed vectors. Independently, an involution inverting a fixed-point-free
cubic has its fixed space equal to its displacement space: a fixed vector
v is the displacement of z(v). Rank-nullity gives half the total dimension.

These elementary arguments supply the order-five and rank-six inputs on
the literal P/U in Aschbacher–Smith, Proposition 8.2.8(6), printed p.719
(PDF p.736 of refs/quasithin.pdf), through TensorRecognition.CodeInputs.
No decomposition into irreducibles or scalar extension is assumed.
-/

public section

open Representation
namespace Representation.CyclicFixedRank
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private lemma binary_neg (v : V) : -v = v := by
  simpa only [CharTwo.neg_eq, one_smul] using (neg_smul (1 : ZMod 2) v).symm

/-- Every fixed vector is the displacement of its image under the cubic. -/
theorem ker_eq_range_of_inverted_cubic (ρ : Representation (ZMod 2) G V) (z s : G)
    (hz : z ^ 3 = 1) (hs : s ^ 2 = 1) (hi : s * z = z ^ 2 * s)
    (hf : ∀ v, ρ z v = v → v = 0) :
    LinearMap.ker (ρ s - LinearMap.id) = LinearMap.range (ρ s - LinearMap.id) := by
  have hz3 (v : V) : ρ z (ρ z (ρ z v)) = v := by
    change (ρ z * (ρ z * ρ z)) v = v
    rw [← map_mul, ← map_mul]
    rw [show z * (z * z) = z ^ 3 by simp [pow_succ, mul_assoc], hz, map_one, Module.End.one_apply]
  have hs2 (v : V) : ρ s (ρ s v) = v := by
    change (ρ s * ρ s) v = v
    rw [← map_mul]
    rw [← pow_two, hs, map_one, Module.End.one_apply]
  have hn (v : V) : v + ρ z v + ρ z (ρ z v) = 0 := by
    apply hf
    simp only [map_add, hz3]
    abel
  have hz2 (v : V) : ρ z (ρ z v) = v + ρ z v := by
    simpa only [neg_add, binary_neg] using eq_neg_of_add_eq_zero_right (hn v)
  have hsi (v : V) : ρ s (ρ z v) = ρ z (ρ z (ρ s v)) := by
    change (ρ s * ρ z) v = (ρ z * (ρ z * ρ s)) v
    rw [← map_mul, ← map_mul, ← map_mul]
    rw [hi, pow_two, mul_assoc]
  ext v
  constructor
  · intro hv
    have hv' : ρ s v = v := sub_eq_zero.mp hv
    refine ⟨ρ z v, ?_⟩
    change ρ s (ρ z v) - ρ z v = v
    rw [hsi, hv', hz2, add_sub_cancel_right]
  · rintro ⟨w, rfl⟩
    change ρ s (ρ s w - w) - (ρ s w - w) = 0
    rw [map_sub, hs2, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg,
      binary_neg, binary_neg, binary_neg]
    have h (v : V) : v + v = 0 := by
      simpa only [binary_neg] using add_neg_cancel v
    abel_nf
    simp only [two_zsmul, h]
/-- An involution inverting a fixed-point-free cubic fixes half the binary space. -/
theorem twice_fixedRank_of_inverted_cubic [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (z s : G)
    (hz : z ^ 3 = 1) (hs : s ^ 2 = 1) (hi : s * z = z ^ 2 * s)
    (hf : ∀ v, ρ z v = v → v = 0) :
    2 * Module.finrank (ZMod 2) (LinearMap.ker (ρ s - LinearMap.id)) =
      Module.finrank (ZMod 2) V := by
  have h := (ρ s - LinearMap.id).finrank_range_add_finrank_ker
  rw [← ker_eq_range_of_inverted_cubic ρ z s hz hs hi hf] at h
  omega

end Representation.CyclicFixedRank

open Representation Representation.BinaryOffender Subgroup
namespace Representation.CyclicFixedRank
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Cyclic commutators are exactly the image of the generator minus the identity. -/
theorem commutator_eq_range (ρ : Representation (ZMod 2) G V) (x : G) :
    subspaceCommutator ρ ⊤ (zpowers x) = LinearMap.range (ρ x - LinearMap.id) := by
  let W := LinearMap.range (ρ x - LinearMap.id)
  let K : Subgroup G := {
    carrier := {g | ∀ v, ρ g v - v ∈ W}
    one_mem' := by intro v; simp only [map_one, Module.End.one_apply, sub_self]; exact W.zero_mem
    mul_mem' := by
      intro a b ha hb v
      have h := W.add_mem (ha (ρ b v)) (hb v)
      simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using h
    inv_mem' := by
      intro a ha v
      have h := W.neg_mem (ha (ρ a⁻¹ v))
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply, neg_sub] using h }
  have hx : x ∈ K := fun v => ⟨v, rfl⟩
  have hK : zpowers x ≤ K := zpowers_le.mpr hx
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    exact hK hg v
  · rintro v ⟨w, rfl⟩
    exact Submodule.subset_span ⟨x, mem_zpowers x, w, Submodule.mem_top, rfl⟩

/-- In finite dimension, cyclic commutator generation excludes all fixed vectors. -/
theorem fixedFree_of_commutator_eq_top [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (x : G)
    (hgen : subspaceCommutator ρ ⊤ (zpowers x) = ⊤) :
    ∀ v, ρ x v = v → v = 0 := by
  rw [commutator_eq_range] at hgen
  have hk : LinearMap.ker (ρ x - LinearMap.id) = ⊥ :=
    LinearMap.ker_eq_bot_iff_range_eq_top.mpr hgen
  intro v hv
  have hm : v ∈ LinearMap.ker (ρ x - LinearMap.id) := sub_eq_zero.mpr hv
  simpa only [hk, Submodule.mem_bot] using hm

end Representation.CyclicFixedRank
