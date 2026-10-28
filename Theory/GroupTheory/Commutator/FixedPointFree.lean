module
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A fixed-point-free actor moves a finite subgroup fully

The commutator map of a fixed-point-free automorphism is surjective.
Consequently a finite subgroup normalized by L equals its commutator
with L if one element of L acts without nontrivial fixed points.

Source application: Aschbacher–Smith9.3.5, the natural tensor plane.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem commutator_eq_of_fixedPointFree (V L : Subgroup G) [Finite V]
    (hVL : L ≤ normalizer (V : Set G)) (l : G) (hl : l ∈ L)
    (hfree : ∀ v ∈ V, Commute l v → v = 1) : ⁅V,L⁆ = V := by
  have hf : MonoidHom.FixedPointFree (V.normalizerMonoidHom ⟨l,hVL hl⟩) := by
    intro v hv
    apply Subtype.ext
    exact hfree v v.property (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hv))
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hVL)
  intro v hv
  obtain ⟨a,ha⟩ := hf.commutatorMap_surjective (⟨v,hv⟩ : V)
  have he : (a : G) / (l * (a : G) * l⁻¹) = v := congrArg Subtype.val ha
  rw [←he]
  simpa only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc]
    using commutator_mem_commutator a.property hl

end Theory.GroupTheory
