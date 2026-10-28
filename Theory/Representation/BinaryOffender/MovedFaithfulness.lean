module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Faithfulness on displacements of a normal self-centralizing layer

A normal kernel fixing all K-displacements meets K in a normal two-group:
its displacement operators square to zero on a binary module. If the ambient
two-core is trivial, that intersection vanishes. Normality then makes the
kernel centralize K, so self-centralization of K kills it altogether.
This is the faithful moved-module reduction used in Aschbacher–Smith
B.6.10 and E.2.3, printed pp.117 and216–217.
-/
public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
theorem normal_eq_bot_of_fixes_displacements
    (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (K N : Subgroup G) [K.Normal] [N.Normal]
    (hK : centralizer (K : Set G) ≤ K)
    (hfix : ∀ n ∈ N, ∀ k ∈ K, ∀ v, ρ n (ρ k v - v) = ρ k v - v) : N = ⊥ := by
  have htwo : IsPGroup 2 (N ⊓ K : Subgroup G) := by
    intro a
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change (a : G) ^ 2 = 1
    apply hρ
    apply LinearMap.ext
    intro v
    have ha := hfix a a.property.1 a a.property.2 v
    have hneg (w : V) : -w = w := by
      have hz : w + w = 0 := by
        simpa only [add_smul, one_smul, zero_smul] using
          congrArg (fun c : ZMod 2 => c • w) (by decide : (1 : ZMod 2) + 1 = 0)
      exact neg_eq_iff_add_eq_zero.mpr hz
    simp only [sub_eq_add_neg, hneg, map_add] at ha
    have hh : ρ a (ρ a v) = v := add_right_cancel (ha.trans (add_comm _ _))
    simpa only [pow_two, map_mul, map_one, Module.End.mul_apply, Module.End.one_apply] using hh
  have hNK : N ⊓ K = ⊥ := by
    apply le_bot_iff.mp
    rw [← hcore]
    exact le_sSup ⟨inferInstance,htwo⟩
  have hc : N ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint (disjoint_iff.mpr hNK))
  apply le_bot_iff.mp
  intro n hn
  exact hNK.le ⟨hn,hK (hc hn)⟩
end Representation.BinaryOffender

