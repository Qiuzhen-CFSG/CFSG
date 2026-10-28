module

public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry

/-!
# Recovering native octads and binary center actors

Fixing the class of an octad word forces a Mathieu permutation to stabilize
that octad. A constant difference between two octad words vanishes at a
point outside their union, so equality in the code quotient lifts to equality
of the words.

For a faithful action with displacements in one binary line, a nonidentity
actor is determined by its fixed hyperplane. Indeed two nonzero linear maps
into a binary line with nested kernels are equal. These facts recover the
involution from the native four-space in H.16.2.

Source: Aschbacher--Smith, H.16.2(5--6), printed pp.402--403.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative

namespace MathieuCode.SectionAction

/-- The stabilizer of the literal octad code vector is exactly its setwise stabilizer. -/
theorem octadVector_fixed_iff (O : Octad) (g : M24) :
    codeRepresentation g (octadVector O) = octadVector O ↔ g ∈ octadStabilizer O := by
  constructor
  · intro hv
    unfold octadVector at hv
    rw [codeRepresentation_mk] at hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      ((Submodule.Quotient.eq codeLine).mp hv)
    change c • BinaryPermutation.allOne (Fin 24) =
      BinaryPermutation.representation (Fin 24) g.val (wordOfSet O.val) - wordOfSet O.val at hc
    rw [permute_wordOfSet] at hc
    change c • BinaryPermutation.allOne (Fin 24) =
      wordOfSet (g • O.val) - wordOfSet O.val at hc
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show (g • O.val ∪ O.val).card < (Finset.univ : Finset (Fin 24)).card by
        have hle := Finset.card_union_le (g • O.val) O.val
        rw [Finset.card_smul_finset, m24Blocks_card _ O.property] at hle
        simpa using (show (g • O.val ∪ O.val).card < 24 by omega))
    have hj' : j ∉ g • O.val ∧ j ∉ O.val := by simpa using hj
    have hc0 := congrFun hc j
    simp [BinaryPermutation.allOne, wordOfSet, hj'.1, hj'.2] at hc0
    rw [hc0, zero_smul] at hc
    have he := sub_eq_zero.mp hc.symm
    change g • O.val = O.val
    apply Finset.ext
    intro i
    have hi := congrFun he i
    by_cases hgi : i ∈ g • O.val <;> by_cases hoi : i ∈ O.val <;>
      simp_all [wordOfSet]
  · intro hg
    exact octadVector_fixed_stabilizer O ⟨g, hg⟩

end MathieuCode.SectionAction

namespace Representation.BinaryOffender

private theorem line_nonzero_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (L : Submodule (ZMod 2) V) (hd : Module.finrank (ZMod 2) L = 1)
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : x = y := by
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hd hx hx0] at hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  fin_cases c
  · change (0 : ZMod 2) • x ≠ 0 at hy0
    exact (hy0 (zero_smul _ _)).elim
  · change x = (1 : ZMod 2) • x
    exact (one_smul _ _).symm

/-- Nonzero maps into a binary line are determined by their kernels. -/
theorem binary_line_map_eq_of_ker_le {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (L : Submodule (ZMod 2) V) (hd : Module.finrank (ZMod 2) L = 1)
    (f g : W →ₗ[ZMod 2] V) (hf : f.range ≤ L) (hg : g.range ≤ L)
    (hne : g ≠ 0) (hk : f.ker ≤ g.ker) : f = g := by
  obtain ⟨v, hv⟩ : ∃ v, g v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (LinearMap.ext hn)
  have hfv : f v ≠ 0 := fun h => hv (hk h)
  have he := line_nonzero_eq L hd (hf ⟨v, rfl⟩) (hg ⟨v, rfl⟩) hfv hv
  ext w
  by_cases hw : f w = 0
  · exact hw.trans (hk hw).symm
  · have hew := line_nonzero_eq L hd (hf ⟨w, rfl⟩) (hf ⟨v, rfl⟩) hw hfv
    have hz : w - v ∈ f.ker := by simp [LinearMap.mem_ker, hew]
    have hgz : g w = g v := sub_eq_zero.mp (by simpa using hk hz)
    exact hew.trans (he.trans hgz.symm)

/-- In a faithful common-center action, containment of fixed hyperplanes
identifies the nonidentity actors. -/
theorem binary_center_action_eq_of_fixed_le {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (W L : Submodule (ZMod 2) V) (hL : Module.finrank (ZMod 2) L = 1)
    (hd : ∀ a ∈ K, ∀ v ∈ W, ρ a v - v ∈ L)
    (hf : subspaceKernel ρ W K = ⊥)
    (a b : G) (ha : a ∈ K) (hb : b ∈ K) (hb1 : b ≠ 1)
    (hfix : W ⊓ fixedSpace ρ (Subgroup.zpowers a) ≤
      W ⊓ fixedSpace ρ (Subgroup.zpowers b)) : a = b := by
  let f : W →ₗ[ZMod 2] V := (ρ a - LinearMap.id).comp W.subtype
  let g : W →ₗ[ZMod 2] V := (ρ b - LinearMap.id).comp W.subtype
  have he : f = g := by
    apply binary_line_map_eq_of_ker_le L hL
    · rintro _ ⟨v, rfl⟩
      exact hd a ha v v.property
    · rintro _ ⟨v, rfl⟩
      exact hd b hb v v.property
    · intro hzero
      apply hb1
      have hm : b ∈ subspaceKernel ρ W K := ⟨hb, fun v hv =>
        sub_eq_zero.mp (LinearMap.congr_fun hzero ⟨v, hv⟩)⟩
      simpa only [hf, Subgroup.mem_bot] using hm
    · intro v hv
      exact sub_eq_zero.mpr ((mem_fixedSpace_zpowers_iff ρ b v).mp
        (hfix ⟨v.property, (mem_fixedSpace_zpowers_iff ρ a v).mpr (sub_eq_zero.mp hv)⟩).2)
  have hba : b⁻¹ * a ∈ subspaceKernel ρ W K := by
    refine ⟨K.mul_mem (K.inv_mem hb) ha, ?_⟩
    intro v hv
    have he' : ρ a v = ρ b v := sub_left_inj.mp (LinearMap.congr_fun he ⟨v, hv⟩)
    rw [map_mul, Module.End.mul_apply, he']
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  rw [hf, Subgroup.mem_bot, inv_mul_eq_one] at hba
  exact hba.symm

end Representation.BinaryOffender
