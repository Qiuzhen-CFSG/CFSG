module

public import Theory.GroupAction.FourGroupCoreAction.Kernel.FixedCores

/-!
# The action after quotienting by the fixed-core product

In the literal quotient `Y/P`, the two point-core images have order two,
generate the quotient, and are conjugate inside it. The descended action on
the original four-group is surjective and has central kernel. Its target has
order six, so the quotient has order at least six.

These facts supply every input of the dihedral step in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
A.1.14(1), printed p.23. Triviality of this central kernel is not assumed or
asserted here: it still requires the conjugate-reflection argument.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
noncomputable section
namespace FourGroupCorePair
variable {G : Type*} [Group G] {V : Subgroup G} {v₁ v₂ : G}
variable (h : FourGroupCorePair V v₁ v₂)

/-- The literal quotient Y/P, carrying the source witness in its type so that
its group structure uses precisely the proved relative normality. -/
def KernelQuotient (_h : FourGroupCorePair V v₁ v₂) :=
  generated v₁ v₂ ⧸ (kernelJoin V v₁ v₂).subgroupOf (generated v₁ v₂)

instance kernelQuotientGroup : Group h.KernelQuotient := by
  let := h.kernelJoin_normal_generated
  exact inferInstanceAs (Group (generated v₁ v₂ ⧸
    (kernelJoin V v₁ v₂).subgroupOf (generated v₁ v₂)))

instance kernelQuotientFinite [Finite G] : Finite h.KernelQuotient := by
  unfold KernelQuotient
  infer_instance

/-- The canonical projection to Y/P. -/
def kernelProjection : generated v₁ v₂ →* h.KernelQuotient := by
  let := h.kernelJoin_normal_generated
  exact QuotientGroup.mk' _

theorem kernelProjection_ker : h.kernelProjection.ker =
    (kernelJoin V v₁ v₂).subgroupOf (generated v₁ v₂) := by
  let := h.kernelJoin_normal_generated
  exact QuotientGroup.ker_mk' _

theorem kernelProjection_surjective : Function.Surjective h.kernelProjection := by
  let := h.kernelJoin_normal_generated
  exact QuotientGroup.mk'_surjective _

/-- The original action descended through the fixed-core product. -/
def quotientAction : h.KernelQuotient →* MulAut V := by
  let := h.kernelJoin_normal_generated
  exact QuotientGroup.lift _ h.action (by
    intro x hx
    rw [h.action_ker]
    exact kernelJoin_le_centralizer hx)

@[simp] theorem quotientAction_projection (x : generated v₁ v₂) :
    h.quotientAction (h.kernelProjection x) = h.action x := rfl

theorem quotientAction_surjective [Finite G] : Function.Surjective h.quotientAction := by
  intro a
  obtain ⟨y, hy⟩ := h.action_surjective a
  exact ⟨h.kernelProjection y, hy⟩

theorem quotientAction_ker_le_center :
    h.quotientAction.ker ≤ center (h.KernelQuotient) := by
  let := h.kernelJoin_normal_generated
  intro x hx
  obtain ⟨y, rfl⟩ := h.kernelProjection_surjective x
  have hyker : y ∈ h.action.ker := hx
  rw [h.action_ker] at hyker
  rw [mem_center_iff]
  intro z
  obtain ⟨w, rfl⟩ := h.kernelProjection_surjective z
  apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
  rw [← map_commutatorElement]
  change ⁅y, w⁆ ∈ h.kernelProjection.ker
  rw [h.kernelProjection_ker]
  exact h.centralizer_commutator_generated_le
    (commutator_mem_commutator hyker w.property)

/-- The image of the first point core in the literal quotient Y/P. -/
def firstQuotientCore : Subgroup (h.KernelQuotient) :=
  ((core v₁).subgroupOf (generated v₁ v₂)).map h.kernelProjection

/-- The image of the second point core in the literal quotient Y/P. -/
def secondQuotientCore : Subgroup (h.KernelQuotient) :=
  ((core v₂).subgroupOf (generated v₁ v₂)).map h.kernelProjection

theorem quotientCore_sup : h.firstQuotientCore ⊔ h.secondQuotientCore = ⊤ := by
  let := h.kernelJoin_normal_generated
  rw [firstQuotientCore, secondQuotientCore, ← Subgroup.map_sup, ← subgroupOf_sup (show core v₁ ≤ generated v₁ v₂ from le_sup_left)
    (show core v₂ ≤ generated v₁ v₂ from le_sup_right)]
  change ((generated v₁ v₂).subgroupOf (generated v₁ v₂)).map h.kernelProjection = ⊤
  rw [subgroupOf_self, map_top_of_surjective _ h.kernelProjection_surjective]

private theorem core_projection_ker {v : G} (hvY : core v ≤ generated v₁ v₂)
    (hvP : pointKernel V v ≤ kernelJoin V v₁ v₂) :
    (h.kernelProjection.comp (inclusion hvY)).ker =
      (V.normalizerMonoidHom.comp (inclusion (hvY.trans h.generated_le_normalizer))).ker := by
  let := h.kernelJoin_normal_generated
  ext x
  change inclusion hvY x ∈ h.kernelProjection.ker ↔
    inclusion (hvY.trans h.generated_le_normalizer) x ∈ V.normalizerMonoidHom.ker
  rw [h.kernelProjection_ker, normalizerMonoidHom_ker]
  change (x : G) ∈ kernelJoin V v₁ v₂ ↔ (x : G) ∈ centralizer (V : Set G)
  exact ⟨fun hx => kernelJoin_le_centralizer hx, fun hx => hvP ⟨x.property, hx⟩⟩

private theorem core_projection_range {v : G} (hvY : core v ≤ generated v₁ v₂) :
    (h.kernelProjection.comp (inclusion hvY)).range =
      ((core v).subgroupOf (generated v₁ v₂)).map h.kernelProjection := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨inclusion hvY y, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem firstQuotientCore_card [Finite G] : Nat.card h.firstQuotientCore = 2 := by
  rw [firstQuotientCore, ← h.core_projection_range le_sup_left, ← index_ker,
    h.core_projection_ker le_sup_left le_sup_left, index_ker]
  exact h.core_action_card₁

theorem secondQuotientCore_card [Finite G] : Nat.card h.secondQuotientCore = 2 := by
  rw [secondQuotientCore, ← h.core_projection_range le_sup_right, ← index_ker,
    h.core_projection_ker le_sup_right le_sup_right, index_ker]
  exact h.core_action_card₂

theorem quotientCores_conjugate [Finite G] :
    ∃ y : h.KernelQuotient,
      h.firstQuotientCore.map (MulAut.conj y).toMonoidHom = h.secondQuotientCore := by
  obtain ⟨y, hy, hyv⟩ := h.exists_conjugator h.mem₁ h.mem₂ h.ne_one₁ h.ne_one₂
  let yY : generated v₁ v₂ := ⟨y, hy⟩
  have hc : ((core v₁).subgroupOf (generated v₁ v₂)).map (MulAut.conj yY).toMonoidHom =
      (core v₂).subgroupOf (generated v₁ v₂) := by
    apply map_injective (generated v₁ v₂).subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le (show core v₂ ≤ generated v₁ v₂ from le_sup_right)]
    calc
      ((core v₁).subgroupOf (generated v₁ v₂)).map
          ((generated v₁ v₂).subtype.comp (MulAut.conj yY).toMonoidHom) =
          (((core v₁).subgroupOf (generated v₁ v₂)).map (generated v₁ v₂).subtype).map
            (MulAut.conj y).toMonoidHom := by rw [map_map]; rfl
      _ = core v₂ := by
        rw [map_subgroupOf_eq_of_le (show core v₁ ≤ generated v₁ v₂ from le_sup_left),
          map_core_conj, hyv]
  refine ⟨h.kernelProjection yY, ?_⟩
  rw [firstQuotientCore, secondQuotientCore, map_map]
  calc
    ((core v₁).subgroupOf (generated v₁ v₂)).map
        ((MulAut.conj (h.kernelProjection yY)).toMonoidHom.comp h.kernelProjection) =
        (((core v₁).subgroupOf (generated v₁ v₂)).map (MulAut.conj yY).toMonoidHom).map
          h.kernelProjection := by
      rw [map_map]
      congr 1
    _ = _ := by rw [hc]

theorem six_le_card_kernelQuotient [Finite G] : 6 ≤ Nat.card h.KernelQuotient := by
  let := h.four
  rw [← IsKleinFour.card_mulAut V]
  exact Nat.card_le_card_of_surjective h.quotientAction h.quotientAction_surjective

end FourGroupCorePair
