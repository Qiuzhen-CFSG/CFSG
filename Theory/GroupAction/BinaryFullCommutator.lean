module
public import Theory.GroupAction.BinarySubspaceResidual
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Full binary automorphisms generate every displacement

If an actor induces all automorphisms of an elementary abelian two-group
W of order greater than two, then [F,W]=W. Given w in W, choose x distinct
from 1 and w. Both x and wx are nonidentity, so some induced automorphism
sends x to wx; its commutator with x is w.

The application to Aschbacher--Smith, original 12.2.25, printed p.805,
puts the original hyperplane in the intrinsic signalizer module of its
normalizer's residual.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace BinarySubspaceResidual
variable {G : Type*} [Group G] [Finite G]

theorem commutator_eq_of_full (F W : Subgroup G) [IsElementaryAbelian 2 W]
    (hn : F ≤ normalizer (W : Set G)) (hc : 2 < Nat.card W)
    (hf : Function.Surjective (W.normalizerMonoidHom.comp (inclusion hn))) :
    ⁅F,W⁆ = W := by
  apply le_antisymm (le_normalizer_iff_commutator_le_right.mp hn)
  intro w hw
  have hex : ∃ x : W, x ≠ 1 ∧ x ≠ ⟨w,hw⟩ := by
    by_contra! hh
    have hs : (Set.univ : Set W) ⊆ {1,⟨w,hw⟩} := by
      intro x _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hx : x = 1
      · exact Or.inl hx
      · exact Or.inr (hh x hx)
    have hcard := Set.ncard_le_ncard hs
    have hle : ({1,(⟨w,hw⟩ : W)} : Set W).ncard ≤ 2 := by
      by_cases hw1 : (⟨w,hw⟩ : W) = 1
      · simp [hw1]
      · simp [Ne.symm hw1]
    rw [Set.ncard_univ] at hcard
    omega
  obtain ⟨x,hx,hxw⟩ := hex
  have hy : (⟨w,hw⟩ : W)*x ≠ 1 := by
    intro he
    have hx2 : x*x = 1 := by
      simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) x
    exact hxw (mul_right_cancel (hx2.trans he.symm))
  obtain ⟨a,ha⟩ := exists_automorphism x ((⟨w,hw⟩ : W)*x) hx hy
  obtain ⟨f,hf⟩ := hf a
  have hact : (f : G)*(x : G)*(f : G)⁻¹ = w*(x : G) := by
    exact congrArg Subtype.val ((MulEquiv.congr_fun hf x).trans ha)
  have he : ⁅(f : G),(x : G)⁆ = w := by
    rw [commutatorElement_def,hact,mul_inv_cancel_right]
  exact he ▸ commutator_mem_commutator f.property x.property
end BinarySubspaceResidual
