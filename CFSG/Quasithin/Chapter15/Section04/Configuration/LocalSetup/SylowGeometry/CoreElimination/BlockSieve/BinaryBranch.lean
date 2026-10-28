module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.SourceComparison
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryLinear.SmallSections

/-!
# The faithful source action in the binary automorphism branch

The internal conjugation module and the actual Sylow subgroup are transported
through the given equivalence H/O₂(H) ≃ Aut(PSLₙ(𝔽₂)). The action formula and
the maximum-elementary origin of its offender are preserved. Comparing this
action with the intrinsic core action transfers the source Sylow fixed-space
obstruction, which excludes both compatible small central-section structures.

These results apply to either binary alternative, n=4 and n=5. They do not
classify an arbitrary FF-representation of these automorphism groups. That
classification still has to construct a small section before the binary branch
can be eliminated. In particular no module classification is attributed to
C.2.7(h), whose conclusion concerns a quotient and a parabolic subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.4.20,
printed p.1164; C.2.7(h), p.145; B.5.1, p.99.
-/

@[expose] public section

open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch
variable {G : Type*} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

private theorem source_offender (h : Input d i j H U K) :
    let V := TwoFactors.FFBranch.moduleClosure (d.Z.subgroupOf H)
    let := h.module_properties.1
    ∃ A ∈ elementaryAbelianMaxSubgroups (h.placed.sylow : Subgroup H),
      ¬ A ≤ pCore 2 H ∧
      IsOffender (coreAction V h.module_properties.2.2.2)
        (A.map (QuotientGroup.mk' (pCore 2 H))) := by
  obtain ⟨_, _, _, _, _, hV, ρ, _, hρ, A, hA, hAQ, hOff⟩ :=
    source_internal_module d.T H K U d.Z (d.X i) h.placed.sylow
      h.placed.sylow_image h.placed.upper.le h.placed.baumann_le h.seed
      h.seed_centralizer h.K_le h.K_normalized h.generation h.characteristic_two
      ((d.X_le_I i j).trans h.placed.overgroup.2)
      (by simpa only [← h.thompson] using h.factor_commutator)
      h.placed.first_quotient_card
  let := h.module_properties.1
  have heq : ρ = coreAction _ h.module_properties.2.2.2 := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (hρ x v).trans (congrArg Subtype.val
      (coreAction_apply _ h.module_properties.2.2.2 x v)).symm
  exact ⟨A, hA, hAQ, heq ▸ hOff⟩

/-- The actual quotient conjugation action, transported by the given isomorphism. -/
noncomputable def action (h : Input d i j H U K) {n : ℕ}
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    letI := h.module_properties.1
    Representation (ZMod 2) (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))
      (Additive (TwoFactors.FFBranch.moduleClosure (d.Z.subgroupOf H))) :=
  letI := h.module_properties.1
  (coreAction _ h.module_properties.2.2.2).comp e.symm.toMonoidHom

/-- The image of the actual source Sylow subgroup under the same quotient map. -/
def sylow (h : Input d i j H U K) {n : ℕ}
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    Sylow 2 (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :=
  h.placed.sylow.mapSurjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

theorem sylow_coe (h : Input d i j H U K) {n : ℕ}
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    (sylow h e : Subgroup _) =
      ((h.placed.sylow : Subgroup H).map (QuotientGroup.mk' _)).map e.toMonoidHom := by
  rw [map_map]
  rfl

theorem action_injective (h : Input d i j H U K) {n : ℕ}
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    letI := h.module_properties.1
    Function.Injective (action h e) := by
  let := h.module_properties.1
  exact (coreAction_injective _ h.module_properties.2.2.2).comp e.symm.injective

theorem action_apply (h : Input d i j H U K) {n : ℕ}
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    letI := h.module_properties.1
    ∀ (x : H) (v : Additive (TwoFactors.FFBranch.moduleClosure (d.Z.subgroupOf H))),
      (((action h e (e (QuotientGroup.mk' _ x)) v).toMul : H) : G) =
        (x : G) * ((v.toMul : H) : G) * (x : G)⁻¹ := by
  let := h.module_properties.1
  intro x v
  change (((coreAction _ h.module_properties.2.2.2 (e.symm (e _)) v).toMul : H) : G) = _
  rw [e.symm_apply_apply]
  exact congrArg Subtype.val (coreAction_apply _ h.module_properties.2.2.2 x v)

theorem exists_offender (h : Input d i j H U K) {n : ℕ}
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    letI := h.module_properties.1
    ∃ A ∈ elementaryAbelianMaxSubgroups (h.placed.sylow : Subgroup H),
      ¬ A ≤ pCore 2 H ∧ IsOffender (action h e)
        ((A.map (QuotientGroup.mk' (pCore 2 H))).map e.toMonoidHom) := by
  let := h.module_properties.1
  obtain ⟨A, hA, hn, ho⟩ := source_offender h
  refine ⟨A, hA, hn, ho.map_equivariant _ (action h e) e.toMonoidHom e.injective
    (LinearEquiv.refl (ZMod 2) _) ?_⟩
  intro g v
  change coreAction _ h.module_properties.2.2.2 g v =
    coreAction _ h.module_properties.2.2.2 (e.symm (e g)) v
  rw [e.symm_apply_apply]

theorem action_isFFModule (h : Input d i j H U K) {n : ℕ}
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    letI := h.module_properties.1
    IsFFModule (action h e) := by
  let := h.module_properties.1
  obtain ⟨A, _, _, hA⟩ := exists_offender h e
  exact ⟨_, hA⟩

theorem no_fixedSpace_enlargement (h : Input d i j H U K) {n : ℕ}
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    letI := h.module_properties.1
    ∀ c, c ∉ sylow h e →
      (∀ v ∈ fixedSpace (action h e) (sylow h e : Subgroup _), action h e c v = v) → False := by
  let := h.module_properties.1
  intro c hc hfix
  apply h.no_fixedSpace_enlargement (e.symm c)
  · intro hm
    apply hc
    change c ∈ (sylow h e : Subgroup _)
    rw [sylow_coe]
    exact ⟨e.symm c, hm, e.apply_symm_apply c⟩
  · intro v hv
    apply hfix v
    intro a
    obtain ⟨x, hx, hxa⟩ := a.property
    change action h e a.val v = v
    rw [← hxa]
    change coreAction _ h.module_properties.2.2.2
      (e.symm (e (QuotientGroup.mk' _ x))) v = v
    rw [e.symm_apply_apply]
    exact hv ⟨_, mem_map_of_mem _ hx⟩

/-- The actual source action has neither of the compatible small central
sections. The FF classification must construct one to eliminate the branch. -/
theorem not_smallSection (h : Input d i j H U K) {n : ℕ}
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    letI := h.module_properties.1
    ¬ Representation.BinaryLinearSections.HasSmallSection (action h e) := by
  let := h.module_properties.1
  intro hs
  let : Finite (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :=
    Finite.of_surjective e e.surjective
  obtain ⟨c, hc, _, hfix⟩ := hs.sylow_enlargement (action h e) (sylow h e)
  exact no_fixedSpace_enlargement h e c hc hfix

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch
