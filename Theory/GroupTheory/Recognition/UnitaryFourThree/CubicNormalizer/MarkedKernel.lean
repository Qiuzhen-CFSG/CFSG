module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.ElementaryKernel

/-!
# The literal Sylow-three consumer of the reflected odd-kernel argument

The marking lists only the original local dihedral actors, their conjugation
on X, and the earlier involution fusion. The consumer retains the actual
Sylow inclusion in C_G(z) and returns the canonical odd kernel. It eliminates
all centralizer, dimension, and elementary-module premises from this stage;
the marking itself is the earlier45.3–45.6 binary-local source input.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma45.7, printed p.245.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G]
namespace CubicNormalizer
structure ReflectedMarking (z : G) (X : Subgroup G) where
  t : G
  s : G
  t_order : orderOf t=2
  s_order : orderOf s=2
  t_normalizes : t∈normalizer (X:Set G)
  s_normalizes : s∈normalizer (X:Set G)
  zt_commute : Commute z t
  t_fused : IsConj z t
  reflection_conjugation : s*t*s⁻¹=t*z
  common_fixed_card : Nat.card (X⊓Subgroup.centralizer ({t}:Set G) : Subgroup G)=3
  rotation_inverts : ∀x∈X,(s*t)*x*(s*t)⁻¹=x⁻¹
end CubicNormalizer
namespace IsType
variable [Finite G] {z:G} (h : IsType z)
include h in
theorem reflected_kernel (P : Sylow 3 (centralizer z))
    (m : CubicNormalizer.ReflectedMarking z
      ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) :
    let X := (P:Subgroup (centralizer z)).map (centralizer z).subtype
    let V := CubicNormalizer.oddKernel X
    IsElementaryAbelian 3 V ∧ (V=X ∨ Nat.card V=81) := by
  let X := (P:Subgroup (centralizer z)).map (centralizer z).subtype
  have hX : Nat.card X=9 := h.cubic_sylow_image_card P
  have hXH : X≤centralizer z := map_subtype_le _
  refine ⟨h.cubic_oddKernel_elementary X hX hXH m.t m.s m.t_order m.s_order
    m.t_normalizes m.zt_commute m.t_fused m.s_normalizes m.reflection_conjugation
    m.common_fixed_card m.rotation_inverts,?_⟩
  rcases h.cubic_oddKernel_card X hX hXH m.t m.s m.t_order m.t_normalizes
    m.zt_commute m.t_fused m.s_normalizes m.reflection_conjugation m.common_fixed_card with h9 | h81
  · left
    have hle : X≤CubicNormalizer.oddKernel X :=
      (h.toCentralizerHypothesis.cubic_oddKernel_fixed X hX hXH).ge.trans inf_le_left
    exact (eq_of_le_of_card_ge hle (by rw [h9,hX])).symm
  · exact Or.inr h81
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
