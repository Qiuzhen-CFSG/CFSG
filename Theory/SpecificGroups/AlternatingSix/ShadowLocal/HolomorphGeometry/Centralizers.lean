module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry.Coordinates

/-!
# Centralizers in the local holomorph

The center and the centralizers of the inner dihedral, transposition and
cyclic-four subgroups are computed on the 32 concrete elements. The last
centralizer is identified with C₈ ⋊ C₂, where the involution acts by the
fifth-power automorphism: the modular group of order 16.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, pp.568–570.
-/

@[expose] public section
namespace AlternatingSix.ShadowLocal.Holomorph
open Subgroup
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 2000000

theorem center_model : center Model = centralTwo := by
  ext x
  simp only [mem_center_iff, mem_centralTwo]
  revert x
  decide +kernel

instance centralTwo_normal : centralTwo.Normal := by
  rw [← center_model]
  infer_instance

theorem centralizer_innerD : centralizer (innerD : Set Model) =
    centralTwo ⊔ transpositionSubgroup := by
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, mem_innerD,
    mem_centralTwo_sup_transposition]
  revert x
  decide +kernel

noncomputable def centralizerInnerEquiv :
    centralizer (innerD : Set Model) ≃* E4 :=
  (MulEquiv.subgroupCongr (centralizer_innerD.trans
    centralTranspositionEmbedding_range.symm)).trans
    (MonoidHom.ofInjective centralTranspositionEmbedding_injective).symm

theorem centralizer_transpositionSubgroup :
    centralizer (transpositionSubgroup : Set Model) = natural := by
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, mem_transpositionSubgroup, mem_natural]
  revert x
  decide +kernel

noncomputable def centralizerTranspositionEquiv :
    centralizer (transpositionSubgroup : Set Model) ≃* (C2 × DihedralGroup 4) :=
  (MulEquiv.subgroupCongr centralizer_transpositionSubgroup).trans naturalEquiv

/-- The action of the involution in the modular group is multiplication by 5. -/
def multiplierFive : C2 →* (ZMod 8)ˣ where
  toFun i := five ^ i.toAdd.val
  map_one' := rfl
  map_mul' := by decide +kernel

abbrev modularAction := unitAction.comp multiplierFive
abbrev Modular16 := Multiplicative (ZMod 8) ⋊[modularAction] C2

instance instFintypeModular16 : Fintype Modular16 :=
  Fintype.ofEquiv (Multiplicative (ZMod 8) × C2) SemidirectProduct.equivProd.symm

/-- The actual semidirect-product inclusion, fixing the rotation. -/
def modularEmbedding : Modular16 →* Model :=
  SemidirectProduct.map (MonoidHom.id _) multiplierFive (by intro i; rfl)

theorem modularEmbedding_injective : Function.Injective modularEmbedding := by decide +kernel

theorem modularEmbedding_range :
    modularEmbedding.range = closure {rotation, transposition} := by
  apply le_antisymm
  · rintro x ⟨i, rfl⟩
    have hf : ∀ i : Modular16, modularEmbedding i =
        rotation ^ i.left.toAdd.val * transposition ^ i.right.toAdd.val := by decide +kernel
    rw [hf]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (subset_closure (by simp)) _)
  · apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨SemidirectProduct.inl (.ofAdd 1), by decide +kernel⟩
    · exact ⟨SemidirectProduct.inr (.ofAdd 1), by decide +kernel⟩

theorem centralizer_cyclicFour :
    centralizer (cyclicFour : Set Model) = closure {rotation, transposition} := by
  rw [← modularEmbedding_range]
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, mem_cyclicFour, MonoidHom.mem_range]
  revert x
  decide +kernel

noncomputable def centralizerFourEquiv :
    centralizer (cyclicFour : Set Model) ≃* Modular16 :=
  (MulEquiv.subgroupCongr (centralizer_cyclicFour.trans modularEmbedding_range.symm)).trans
    (MonoidHom.ofInjective modularEmbedding_injective).symm

theorem card_modular16 : Nat.card Modular16 = 16 := by
  rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide +kernel

theorem modular_action_generator (x : Multiplicative (ZMod 8)) :
    modularAction (Multiplicative.ofAdd 1) x = x ^ 5 := by
  revert x
  decide +kernel

/-- No noncentral inner-dihedral involution is a square in the whole model. -/
theorem inner_involution_not_square (e : Model) (heD : e ∈ innerD)
    (heZ : e ∉ centralTwo) (he2 : e ^ 2 = 1) : ∀ x : Model, x ^ 2 ≠ e := by
  revert e
  simp only [mem_innerD, mem_centralTwo]
  decide +kernel

/-- Either noncentral element of `C(D)` has the same centralizer as `P₀`. -/
theorem centralizer_innerCentralizer_involution (u : Model)
    (hu : u ∈ centralizer (innerD : Set Model)) (huZ : u ∉ centralTwo)
    (hu2 : u ^ 2 = 1) :
    centralizer ({u} : Set Model) = centralizer (transpositionSubgroup : Set Model) := by
  rw [centralizer_innerD, mem_centralTwo_sup_transposition] at hu
  rw [mem_centralTwo] at huZ
  rw [centralizer_transpositionSubgroup]
  ext x
  simp only [mem_centralizer_singleton_iff, mem_natural]
  have h : ∀ u x : Model, (∃ i : E4, centralTranspositionEmbedding i = u) →
      (¬ ∃ i : C2, centralEmbedding i = u) → u ^ 2 = 1 →
      (x * u = u * x ↔ ∃ i : C2 × DihedralGroup 4, naturalEmbedding i = x) := by
    decide +kernel
  exact h u x hu huZ hu2

end AlternatingSix.ShadowLocal.Holomorph
