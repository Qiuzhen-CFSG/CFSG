module

public import Theory.GroupTheory.GeneralizedThompsonTransfer
import Mathlib.Tactic.Group

/-!
# Fusion of commuting pairs and generalized transfer

If C(w) controls the fusion of z into C(w), then C(z) controls the
fusion of w into C(z). Conjugate the pair so its second entry is w,
correct the first entry inside C(w), and conjugate back.

For an involution w in the odd-index centralizer C(z), this correction
makes its image in every abelian quotient of C(z) invariant under ambient
fusion. Generalized transfer then detects w whenever that image is nontrivial.

Source: Aschbacher--Smith, Lemma 14.3.22, printed p.999, and A.1.37(2).
No splitting of the entire involution centralizer is required.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup
variable {G : Type*} [Group G]

/-- Fusion of one commuting class in a centralizer is symmetric in the two classes. -/
public theorem centralizer_fusion_symmetric {z w : G}
    (hf : ∀ a ∈ centralizer ({w} : Set G), IsConj z a →
      ∃ c ∈ centralizer ({w} : Set G), c * z * c⁻¹ = a) :
    ∀ b ∈ centralizer ({z} : Set G), IsConj w b →
      ∃ c ∈ centralizer ({z} : Set G), c * w * c⁻¹ = b := by
  intro b hb hwb
  obtain ⟨g, hg⟩ := isConj_iff.mp hwb
  have hbz : b * z = z * b := mem_centralizer_singleton_iff.mp hb
  have ha : g⁻¹ * z * g ∈ centralizer ({w} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hw : w = g⁻¹ * b * g := by rw [← hg]; simp [mul_assoc]
    rw [hw]
    simp only [mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc z b, ← hbz]
    simp [mul_assoc]
  obtain ⟨c, hc, he⟩ := hf (g⁻¹ * z * g) ha
    (isConj_iff.mpr ⟨g⁻¹, by simp⟩)
  refine ⟨g * c, ?_, ?_⟩
  · apply mem_centralizer_singleton_iff.mpr
    have hh : (g * c) * z * (g * c)⁻¹ = z := by
      calc
        _ = g * (c * z * c⁻¹) * g⁻¹ := by group
        _ = z := by rw [he]; group
    exact mul_inv_eq_iff_eq_mul.mp hh
  · have hw := mem_centralizer_singleton_iff.mp hc
    calc
      _ = g * (c * w * c⁻¹) * g⁻¹ := by group
      _ = g * w * g⁻¹ := by rw [hw]; group
      _ = b := hg

/-- Opposite centralizer fusion supplies the exact coset condition for generalized transfer. -/
public theorem not_mem_commutator_of_opposite_centralizer_fusion [Finite G]
    (z w : G) (hwz : w ∈ centralizer ({z} : Set G))
    (N : Subgroup (centralizer ({z} : Set G))) [N.Normal]
    [IsMulCommutative ((centralizer ({z} : Set G)) ⧸ N)]
    (hindex : Nat.Coprime 2 (centralizer ({z} : Set G)).index)
    (hw : orderOf w = 2) (hnot : (⟨w, hwz⟩ : centralizer ({z} : Set G)) ∉ N)
    (hf : ∀ a ∈ centralizer ({w} : Set G), IsConj z a →
      ∃ c ∈ centralizer ({w} : Set G), c * z * c⁻¹ = a) :
    w ∉ _root_.commutator G := by
  let H := centralizer ({z} : Set G)
  let wH : H := ⟨w, hwz⟩
  apply Subgroup.not_mem_commutator_of_involution_fusion (G := G) N wH hindex
    (by simpa only [← Subgroup.orderOf_coe] using hw) hnot
  intro x hx
  obtain ⟨c, hc, he⟩ := centralizer_fusion_symmetric hf x x.property hx
  let cH : H := ⟨c, hc⟩
  have heH : cH * wH * cH⁻¹ = x := Subtype.ext he
  apply (QuotientGroup.eq_one_iff (N := N) (wH⁻¹ * x)).mp
  change QuotientGroup.mk' N (wH⁻¹ * x) = 1
  rw [map_mul, map_inv, ← heH, map_mul, map_mul, map_inv]
  exact by simp [mul_comm]
end Subgroup

