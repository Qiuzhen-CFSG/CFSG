module

public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.SpecificGroups.OrthogonalFourBinary.NonsingularSix
public import Theory.Representation.SpecialLinearNatural
public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines
public import Theory.Representation.NormalElementaryQuotient

/-!
# Simplicity of the two small natural binary actions

SL₂(2) is transitive on nonzero vectors of its natural plane. In the
split orthogonal four-space, a nonzero invariant subspace contains a
nonsingular vector: a suitable conjugate of a singular vector has
nonsingular sum with it. The nonsingular orbit then spans the space.

Compatible coordinates transport these invariant-subspace statements to
the actual centralizer quotient of a normal elementary subgroup. Thus
normal subgroups contained in either natural module are trivial or equal
to the module. This supports the reduced-join argument in
Aschbacher–Smith 14.1.7, printed p.977.
-/

public section

open Subgroup Theory.AlgebraicGroup
open scoped IsMulCommutative
namespace OrthogonalFourBinary

theorem subspace_eq_bot_or_top (W : Submodule F Space)
    (hW : ∀ g : TerminalLines.IsometryGroup, ∀ v ∈ W, g.val v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hz : W = ⊥
  · exact Or.inl hz
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz
  have hn : ∃ u ∈ W, form u = 1 := by
    by_cases hq : form v = 0
    · have hex : ∀ x : Space, x ≠ 0 → form x = 0 →
          ∃ y : Space, y ≠ 0 ∧ form y = 0 ∧ form (x + y) = 1 := by decide +kernel
      obtain ⟨w, hw0, hwq, hsum⟩ := hex v hv0 hq
      obtain ⟨e, he⟩ := exists_isometry_of_singular v w hv0 hw0 hq hwq
      let g : TerminalLines.IsometryGroup := ⟨e.toLinearEquiv,
        (mem_quadraticIsometrySubgroup form _).mpr e.map_app'⟩
      have hw : w ∈ W := he ▸ hW g v hv
      exact ⟨v + w, W.add_mem hv hw, hsum⟩
    · exact ⟨v, hv, (by decide +kernel : ∀ a : F, a ≠ 0 → a = 1) (form v) hq⟩
  obtain ⟨u, hu, hqu⟩ := hn
  apply top_unique
  intro x _
  obtain ⟨a, b, ha, hb, rfl⟩ := sum_two_nonsingular x
  obtain ⟨g, hg⟩ := exists_isometry_of_nonsingular u a hqu ha
  obtain ⟨h, hh⟩ := exists_isometry_of_nonsingular u b hqu hb
  exact W.add_mem (hg ▸ hW g u hu) (hh ▸ hW h u hu)
end OrthogonalFourBinary

namespace Representation

theorem binarySL2_subspace_eq_bot_or_top (W : Submodule (ZMod 2) (Fin 2 → ZMod 2))
    (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), ∀ v ∈ W,
      specialLinearNatural 2 g v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hz : W = ⊥
  · exact Or.inl hz
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · exact hw ▸ W.zero_mem
  obtain ⟨g, hg⟩ := Matrix.SL2.exists_mulVec_eq (ZMod 2) v w hv0 hw
  exact hg ▸ hW g v hv

/-- Compatible coordinates transfer the invariant-subspace dichotomy. -/
theorem subspace_simple_of_coordinates
    {G H V W : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : H → W → W)
    (c : V ≃ₗ[ZMod 2] W) (e : G ≃* H)
    (hc : ∀ g v, c (ρ g v) = σ (e g) (c v))
    (hirr : ∀ A : Submodule (ZMod 2) W,
      (∀ g v, v ∈ A → σ g v ∈ A) → A = ⊥ ∨ A = ⊤)
    (A : Submodule (ZMod 2) V)
    (hA : ∀ g v, v ∈ A → ρ g v ∈ A) : A = ⊥ ∨ A = ⊤ := by
  let B := A.map c.toLinearMap
  have hB : ∀ g v, v ∈ B → σ g v ∈ B := by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨ρ (e.symm g) w, hA _ _ hw, ?_⟩
    change c (ρ (e.symm g) w) = σ g (c w)
    rw [hc, e.apply_symm_apply]
  rcases hirr B hB with h | h
  · left
    apply bot_unique
    intro v hv
    have hm : c v ∈ B := ⟨v, hv, rfl⟩
    rw [h] at hm
    exact c.injective ((Submodule.mem_bot _).mp hm |>.trans (map_zero c).symm)
  · right
    apply top_unique
    intro v _
    have hm : c v ∈ B := h ▸ Submodule.mem_top
    obtain ⟨w, hw, he⟩ := hm
    exact c.injective he ▸ hw

namespace NormalElementaryQuotient
variable {G : Type*} [Group G] (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]

theorem normal_subgroup_eq_bot_or_eq
    (hirr : ∀ W : Submodule (ZMod 2) (Additive V),
      (∀ g v, v ∈ W → representation V (QuotientGroup.mk' (centralizer (V : Set G)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (A : Subgroup G) [A.Normal] (hAV : A ≤ V) : A = ⊥ ∨ A = V := by
  let W := subspace V (A.subgroupOf V)
  have hstable : ∀ g v, v ∈ W → representation V
      (QuotientGroup.mk' (centralizer (V : Set G)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g v ∈ W := by
    intro g v hv
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (centralizer (V : Set G)) g
    change ((representation V (QuotientGroup.mk' (centralizer (V : Set G)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) _ v).toMul : G) ∈ A
    rw [representation_apply]
    exact (inferInstance : A.Normal).conj_mem _ hv a
  rcases hirr W hstable with h | h
  · left
    apply bot_unique
    intro a ha
    have hv : Additive.ofMul (⟨a, hAV ha⟩ : V) ∈ W := ha
    rw [h] at hv
    exact congrArg (fun v : Additive V => (v.toMul : G)) ((Submodule.mem_bot _).mp hv)
  · right
    apply le_antisymm hAV
    intro v hv
    exact show Additive.ofMul (⟨v, hv⟩ : V) ∈ W from h ▸ Submodule.mem_top
end NormalElementaryQuotient
end Representation
