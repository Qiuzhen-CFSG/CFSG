module

public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.Representation.HigherFieldBorelFixedSpaces.Extension
public import Theory.Representation.ElementaryAbelianAction


/-!
# Involutions fixing an odd-index subgroup through two central layers

Suppose Q is normalized by K and C_K(Q) ≤ Q. An involution normalizing K
and centralizing Q has an elementary abelian span under K: its conjugates
differ by elements of Q and commute. If [K,Q] lies in U, the span has two
successive central quotients above U. Odd-index averaging, applied twice,
shows that fixation on a subgroup B of odd index extends to K whenever
B-fixed elements of U are K-fixed. No splitting or cohomology vanishing
is assumed.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
the L₂(4)-block step in 13.6.18, printed p.931 (PDF p.948).
-/

public section
namespace Subgroup.OddIndexInvolutionLayers
open Subgroup
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G]

open Representation Representation.BinaryOffender Representation.HigherFieldBorelFixedSpaces

/-- Odd-index averaging expressed in ambient centralizers. -/
theorem centralizer_lift (K W D : Subgroup G) [IsElementaryAbelian 2 W]
    (hN : K ≤ normalizer (W : Set G)) (B : Subgroup K) (hindex : Odd B.index)
    (hcomm : ⁅K, W⁆ ≤ D)
    (hfixed : D ⊓ centralizer (B.map K.subtype : Set G) ≤ centralizer (K : Set G)) :
    W ⊓ centralizer (B.map K.subtype : Set G) ≤ centralizer (K : Set G) := by
  let f : K →* MulAut W := W.normalizerMonoidHom.comp (inclusion hN)
  let _ := MulDistribMulAction.compHom W f
  let π : Representation (ZMod 2) K (Additive W) := ofElementaryAbelianAction
  let D' : Submodule (ZMod 2) (Additive W) :=
    AddSubgroup.toZModSubmodule 2 (D.subgroupOf W).toAddSubgroup
  have heq : fixedSpace π B = π.invariants := by
    apply odd_index_fixedSpace_extension π B D' hindex
    · intro k w
      change ((k : G) * (w.toMul : G) * (k : G)⁻¹) / (w.toMul : G) ∈ D
      rw [div_eq_mul_inv]
      exact hcomm (commutator_mem_commutator k.property w.toMul.property)
    · intro w hw k
      have hc : (w.toMul : G) ∈ centralizer (B.map K.subtype : Set G) := by
        rintro _ ⟨b, hb, rfl⟩
        have he := congrArg (fun y : Additive W => (y.toMul : G)) (hw.2 ⟨b, hb⟩)
        change (b : G) * (w.toMul : G) * (b : G)⁻¹ = (w.toMul : G) at he
        exact mul_inv_eq_iff_eq_mul.mp he
      have hk := hfixed ⟨hw.1, hc⟩ k k.property
      apply Additive.toMul.injective
      apply Subtype.ext
      change (k : G) * (w.toMul : G) * (k : G)⁻¹ = (w.toMul : G)
      exact mul_inv_eq_iff_eq_mul.mpr hk
  intro w hw k hk
  have hm : Additive.ofMul (⟨w, hw.1⟩ : W) ∈ fixedSpace π B := by
    intro b
    apply Additive.toMul.injective
    apply Subtype.ext
    change (b.val : G) * w * (b.val : G)⁻¹ = w
    exact mul_inv_eq_iff_eq_mul.mpr (hw.2 _ (mem_map_of_mem K.subtype b.property))
  rw [heq] at hm
  have he := congrArg (fun y : Additive W => (y.toMul : G)) (hm ⟨k, hk⟩)
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The relative span of an involution fixing a self-centralizing kernel is elementary. -/
theorem span_elementary (K Q : Subgroup G) (hKQ : K ≤ normalizer (Q : Set G))
    (hself : K ⊓ centralizer (Q : Set G) ≤ Q)
    (a : G) (ha2 : a ^ 2 = 1) (haK : a ∈ normalizer (K : Set G))
    (haQ : a ∈ centralizer (Q : Set G)) :
    IsElementaryAbelian 2 (conjugateSpanBy (zpowers a) K) ∧
      ⁅K, conjugateSpanBy (zpowers a) K⁆ ≤ Q := by
  let W := conjugateSpanBy (zpowers a) K
  have hKW : K ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  have hWQ : W ≤ centralizer (Q : Set G) := by
    apply le_centralizer_iff.mp
    exact le_centralizer_conjugateSpanBy_of_normalizes Q (zpowers a) K hKQ
      (le_centralizer_iff.mp ((zpowers_le).mpr haQ))
  have hWK : W ≤ normalizer (K : Set G) :=
    conjugateSpanBy_le ((zpowers_le).mpr haK)
      (K.le_normalizer.trans (normalizer (K : Set G)).le_normalizer)
  have hcomm : ⁅K, W⁆ ≤ Q := by
    apply le_trans (le_inf ((le_normalizer_iff_commutator_le_left).mp hWK) ?_) hself
    exact (commutator_mono le_rfl hWQ).trans
      ((le_normalizer_iff_commutator_le_right).mp
        (hKQ.trans (normalizer_le_normalizer_centralizer Q)))
  have haW : a ∈ centralizer (W : Set G) := by
    have hspan : W ≤ centralizer ({a} : Set G) := by
      apply (closure_le _).mpr
      rintro _ ⟨k, hk, z, hz, rfl⟩
      have hq : ⁅k, z⁆ ∈ Q := hcomm
        (commutator_mem_commutator hk (le_conjugateSpanBy (zpowers a) K hz))
      have hac : Commute a ⁅k, z⁆ := (haQ _ hq).symm
      have haz : Commute a z :=
        setLike_mul_comm (mem_zpowers a) hz
      apply mem_centralizer_singleton_iff.mpr
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using
        (hac.mul_right haz).eq.symm
    intro w hw
    exact (mem_centralizer_singleton_iff.mp (hspan hw))
  have habel : IsMulCommutative W := by
    apply le_centralizer_iff_isMulCommutative.mp
    exact le_centralizer_conjugateSpanBy_of_normalizes W (zpowers a) K hKW
      (le_centralizer_iff.mp ((zpowers_le).mpr haW))
  let _ : IsMulCommutative (closure {x | ∃ k ∈ K, ∃ z ∈ zpowers a, k * z * k⁻¹ = x}) := habel
  let _ := IsElementaryAbelian.zpowers_of_pow_eq_one ha2
  refine ⟨?_, hcomm⟩
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨k, hk, z, hz, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian z hz, mul_one, mul_inv_cancel]

/-- Two successive central layers above an elementary moving layer. -/
theorem involution_fixed_of_layers (K Q U : Subgroup G)
    (hKQ : K ≤ normalizer (Q : Set G))
    (hself : K ⊓ centralizer (Q : Set G) ≤ Q)
    (hQU : ⁅K, Q⁆ ≤ U)
    (B : Subgroup K) (hindex : Odd B.index)
    (hfixed : U ⊓ centralizer (B.map K.subtype : Set G) ≤ centralizer (K : Set G))
    (a : G) (ha2 : a ^ 2 = 1) (haK : a ∈ normalizer (K : Set G))
    (haQ : a ∈ centralizer (Q : Set G))
    (haB : a ∈ centralizer (B.map K.subtype : Set G)) :
    a ∈ centralizer (K : Set G) := by
  let W := conjugateSpanBy (zpowers a) K
  obtain ⟨hW, hcomm⟩ := span_elementary K Q hKQ hself a ha2 haK haQ
  let _ : IsElementaryAbelian 2 W := hW
  let _ : IsElementaryAbelian 2 (W ⊓ Q : Subgroup G) := IsElementaryAbelian.of_le inf_le_left
  have hKW : K ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  have hKQW : K ≤ normalizer (W ⊓ Q : Subgroup G) :=
    (le_inf hKW hKQ).trans inf_normalizer_le_normalizer_inf
  have hfixedQ : (W ⊓ Q) ⊓ centralizer (B.map K.subtype : Set G) ≤
      centralizer (K : Set G) :=
    centralizer_lift K (W ⊓ Q) U hKQW B hindex
      ((commutator_mono le_rfl inf_le_right).trans hQU) hfixed
  have hfixedW := centralizer_lift K W (W ⊓ Q) hKW B hindex
    (le_inf (le_normalizer_iff_commutator_le_right.mp hKW) hcomm) hfixedQ
  exact hfixedW ⟨le_conjugateSpanBy (zpowers a) K (mem_zpowers a), haB⟩

end Subgroup.OddIndexInvolutionLayers
