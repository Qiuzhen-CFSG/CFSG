module

public import Theory.ElementaryAbelian.BinaryQuotientRank
public import Theory.Representation.FixedSpaceCodimension
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Conjugation fixed spaces of internal binary modules

A subgroup I normalizing an elementary abelian two-subgroup W acts linearly
on Additive W by actual ambient conjugation. Fixed vectors of A ≤ I are
exactly C_W(A). Counting vectors identifies the difference of logarithms of
subgroup orders with the dimension of the linear fixed-space quotient.
The generated-subgroup dimension theorem therefore applies to internal modules
without requiring W to be normal in the ambient group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.17 and
the internal-module applications in B.2.18, printed pp.79–81.
-/

open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryInternalFixedSpaceCodimension
variable {G : Type*} [Group G]

/-- The genuine conjugation representation of a subgroup normalizing W. -/
@[expose] public noncomputable def representation (W I : Subgroup G) [IsElementaryAbelian 2 W]
    (hI : I ≤ normalizer (W : Set G)) : Representation (ZMod 2) I (Additive W) where
  toFun g := (W.normalizerMonoidHom (inclusion hI g)).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro w
    change Additive.ofMul (W.normalizerMonoidHom (inclusion hI 1) w.toMul) = w
    rw [map_one, map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro w
    change Additive.ofMul (W.normalizerMonoidHom (inclusion hI (a * b)) w.toMul) = _
    rw [map_mul, map_mul]
    rfl

/-- Evaluation in the ambient group is conjugation. -/
public theorem representation_apply (W I : Subgroup G) [IsElementaryAbelian 2 W]
    (hI : I ≤ normalizer (W : Set G)) (g : I) (w : Additive W) :
    ((representation W I hI g w).toMul : G) = g * (w.toMul : G) * (g : G)⁻¹ := rfl

/-- Linear fixed vectors are exactly the elements centralizing the acting subgroup. -/
public theorem mem_invariants (W I A : Subgroup G) [IsElementaryAbelian 2 W]
    (hI : I ≤ normalizer (W : Set G)) (hA : A ≤ I) (w : Additive W) :
    w ∈ invariants ((representation W I hI).comp (A.subgroupOf I).subtype) ↔
      (w.toMul : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hw a ha
    have h := congrArg (fun v : Additive W => (v.toMul : G))
      (hw ⟨⟨a, hA ha⟩, ha⟩)
    change a * (w.toMul : G) * a⁻¹ = (w.toMul : G) at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · intro hw a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a : G) * (w.toMul : G) * (a : G)⁻¹ = (w.toMul : G)
    rw [hw a a.property, mul_inv_cancel_right]

private noncomputable def fixedSpaceEquiv (W I A : Subgroup G) [IsElementaryAbelian 2 W]
    (hI : I ≤ normalizer (W : Set G)) (hA : A ≤ I) :
    invariants ((representation W I hI).comp (A.subgroupOf I).subtype) ≃
      (W ⊓ centralizer (A : Set G) : Subgroup G) where
  toFun w := ⟨w.val.toMul, w.val.toMul.property,
    (mem_invariants W I A hI hA w.val).mp w.property⟩
  invFun w := ⟨Additive.ofMul ⟨w, w.property.1⟩,
    (mem_invariants W I A hI hA _).mpr w.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite G]

/-- The logarithmic fixed codimension is the dimension of the actual linear quotient. -/
public theorem fixedCodim_eq_finrank (W I A : Subgroup G) [IsElementaryAbelian 2 W]
    (hI : I ≤ normalizer (W : Set G)) (hA : A ≤ I) :
    Nat.log 2 (Nat.card W) - Nat.log 2 (Nat.card ↥(W ⊓ centralizer (A : Set G))) =
      Module.finrank (ZMod 2) (Additive W ⧸
        invariants ((representation W I hI).comp (A.subgroupOf I).subtype)) := by
  let U := invariants ((representation W I hI).comp (A.subgroupOf I).subtype)
  have hW : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    change Nat.card W = _ at h
    simpa only [Nat.card_zmod] using h
  have hU : Nat.card ↥(W ⊓ centralizer (A : Set G)) =
      2 ^ Module.finrank (ZMod 2) U := by
    rw [← Nat.card_congr (fixedSpaceEquiv W I A hI hA)]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U))
  rw [hW, hU, Nat.log_pow Nat.one_lt_two, Nat.log_pow Nat.one_lt_two]
  have hd := Submodule.finrank_quotient_add_finrank U
  exact Nat.sub_eq_of_eq_add hd.symm

variable {ι : Type*} [Fintype ι]

/-- Thompson’s dimension argument for an internal module invariant under the generated group. -/
public theorem fixed_eq_and_rank_eq_of_sum_le (W : Subgroup G) [IsElementaryAbelian 2 W]
    (X : ι → Subgroup G) (L : Subgroup G)
    (hn : (⨆ i, X i) ≤ normalizer (W : Set G))
    (hL : L ≤ ⨆ i, X i)
    (hd : (∑ i, (Nat.log 2 (Nat.card W) -
      Nat.log 2 (Nat.card ↥(W ⊓ centralizer (X i : Set G))))) ≤
      Nat.log 2 (Nat.card W) - Nat.log 2 (Nat.card ↥(W ⊓ centralizer (L : Set G)))) :
    W ⊓ centralizer (L : Set G) = W ⊓ centralizer ((⨆ i, X i : Subgroup G) : Set G) ∧
      Nat.log 2 (Nat.card W) - Nat.log 2 (Nat.card ↥(W ⊓ centralizer (L : Set G))) =
        ∑ i, (Nat.log 2 (Nat.card W) -
          Nat.log 2 (Nat.card ↥(W ⊓ centralizer (X i : Set G)))) := by
  let I := ⨆ i, X i
  have hX (i : ι) : X i ≤ I := le_iSup X i
  have hgen : (⨆ i, (X i).subgroupOf I) = I.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_iSup, map_subgroupOf_eq_of_le le_rfl]
    simp only [map_subgroupOf_eq_of_le (hX _)]
    rfl
  have hLI : L.subgroupOf I ≤ ⨆ i, (X i).subgroupOf I := by
    rw [hgen]
    exact subgroupOf_mono I hL
  have hd' : (∑ i, Module.finrank (ZMod 2) (Additive W ⧸
        invariants ((representation W I hn).comp ((X i).subgroupOf I).subtype))) ≤
      Module.finrank (ZMod 2) (Additive W ⧸
        invariants ((representation W I hn).comp (L.subgroupOf I).subtype)) := by
    simpa only [← fixedCodim_eq_finrank W I _ hn (hX _),
      ← fixedCodim_eq_finrank W I L hn hL] using hd
  obtain ⟨hfixed, hrank⟩ := (representation W I hn).invariants_eq_and_codimension_eq_of_sum_le
    (fun i => (X i).subgroupOf I) (L.subgroupOf I) hLI hd'
  rw [hgen] at hfixed
  constructor
  · ext w
    constructor
    · intro hw
      refine ⟨hw.1, ?_⟩
      have hv := (mem_invariants W I L hn hL (Additive.ofMul ⟨w, hw.1⟩)).mpr hw.2
      rw [hfixed] at hv
      exact (mem_invariants W I I hn le_rfl _).mp hv
    · intro hw
      refine ⟨hw.1, ?_⟩
      have hv := (mem_invariants W I I hn le_rfl (Additive.ofMul ⟨w, hw.1⟩)).mpr hw.2
      rw [← hfixed] at hv
      exact (mem_invariants W I L hn hL _).mp hv
  · simpa only [← fixedCodim_eq_finrank W I L hn hL,
      ← fixedCodim_eq_finrank W I _ hn (hX _)] using hrank

end Representation.BinaryInternalFixedSpaceCodimension
