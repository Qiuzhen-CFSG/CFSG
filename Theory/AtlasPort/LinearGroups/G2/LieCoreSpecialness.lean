module

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic
public import Theory.Frattini.OmegaProducts
public import Theory.ElementaryAbelian.Quotient

/-!
# Specialness of the actual first G₂ local two-core

The explicit local quotient identifies its two-core with the five-root
radical. Transporting the derived subgroup, Frattini subgroup and center
across that isomorphism gives specialness of the intrinsic core itself.
Its center is the additive field, its order is q⁵, and its center has order q.
The common Sylow subgroup already lies in the local group, so these same
conclusions apply to the source's literal group L₁S, including over F₂.

Source: Aschbacher--Smith, Notation F.1.11 and F.1.12(I)(3), printed p.262.
The root calculations and quotient identification are re-exported from the
licensed ATLAS model and its checked local extensions.
-/

@[expose] public section

namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The center of the intrinsic first core is the additive coefficient field. -/
noncomputable def local₁CoreCenterEquiv :
    Subgroup.center (pCore 2 (local₁ (F := F))) ≃* Multiplicative F :=
  (Subgroup.centerCongr local₁CoreEquivRadical).trans
    (centerEquivHighestRoot radical₁ le_rfl (fiveRootSubgroup_le_unipotent _ _))

/-- Complete special-group structure of the intrinsic first two-core. -/
theorem local₁_pCore_special :
    IsPGroup 2 (pCore 2 (local₁ (F := F))) ∧
    commutator (pCore 2 (local₁ (F := F))) ≠ ⊥ ∧
    commutator (pCore 2 (local₁ (F := F))) = Subgroup.center (pCore 2 (local₁ (F := F))) ∧
    frattini (pCore 2 (local₁ (F := F))) = Subgroup.center (pCore 2 (local₁ (F := F))) ∧
    IsElementaryAbelian 2 (Subgroup.center (pCore 2 (local₁ (F := F)))) ∧
    Nat.card (pCore 2 (local₁ (F := F))) = Nat.card F ^ 5 ∧
    Nat.card (Subgroup.center (pCore 2 (local₁ (F := F)))) = Nat.card F := by
  let e := local₁CoreEquivRadical (F := F)
  have hD : (commutator (pCore 2 (local₁ (F := F)))).map e.toMonoidHom =
      commutator (radical₁ (F := F)) := by
    rw [map_commutator_eq, e.toMonoidHom.range_eq_top_of_surjective e.surjective]
    rfl
  have hcenter : commutator (pCore 2 (local₁ (F := F))) =
      Subgroup.center (pCore 2 (local₁ (F := F))) := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hD, Subgroup.center_map_equiv e, radical₁_commutator_eq_center]
  refine ⟨pCore_isPGroup, ?_, hcenter, ?_, ?_, card_local₁_pCore, ?_⟩
  · intro h
    apply radical₁_commutator_ne_bot (F := F)
    rw [← hD, h, Subgroup.map_bot]
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.frattini_map_equiv e, Subgroup.center_map_equiv e,
      radical₁_frattini_eq_center]
  · let := radical₁_center_elementary (F := F)
    exact IsElementaryAbelian.of_surjective (Subgroup.centerCongr e).symm.toMonoidHom
      (Subgroup.centerCongr e).symm.surjective
  · exact Nat.card_congr local₁CoreCenterEquiv.toEquiv

/-- The special group denoted by q^(1+4) in the source is O₂(L₁S) itself. -/
theorem local₁_sylow_pCore_special :
    let Q := pCore 2 (local₁ (F := F) ⊔ (sylow (F := F) : Subgroup (Model F)) :
      Subgroup (Model F))
    IsPGroup 2 Q ∧ commutator Q ≠ ⊥ ∧
    commutator Q = Subgroup.center Q ∧ frattini Q = Subgroup.center Q ∧
    IsElementaryAbelian 2 (Subgroup.center Q) ∧
    Nat.card Q = Nat.card F ^ 5 ∧ Nat.card (Subgroup.center Q) = Nat.card F := by
  dsimp only
  rw [local₁_sup_sylow]
  exact local₁_pCore_special

/-- The source numbering is fixed by the whole center of the marked Sylow group. -/
theorem local₁_commutator_sylow_center :
    ⁅local₁ (F := F),
      (Subgroup.center (sylow (F := F) : Subgroup (Model F))).map
        (sylow (F := F) : Subgroup (Model F)).subtype⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro g hg
  apply Subgroup.mem_centralizer_iff.mpr
  rintro z ⟨x, hx, rfl⟩
  exact (local₁_centralizes_sylow_center g hg ⟨x, hx⟩).eq.symm

end Atlas.G2.LieParabolicSetup
