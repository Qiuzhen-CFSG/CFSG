module
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.Group
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.BlockModel
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.BlockComparison.Partition

/-!
# The homomorphism on the literal blocks

Generator compatibility with the checked block-label map extends by subgroup
closure to a unique action of E on the 65 blocks. Its image is exactly the
published degree-65 generated subgroup. The two central involutions fix every
block, so the action descends through the literal quotient E/kernel.

The kernel exhaustion is a separate graph argument. Source: the block system
in `AtlasModel/source/blocks.json`, with the conventions and attribution in
`AtlasModel/source/README.md`; Aschbacher--Smith I.1.1 and I.1.3(5), p.407.
-/

public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.BlockComparison
open Data

private theorem exists_action (g : E) :
    ∃ h : BlockModel.Model, ∀ p, blockOf (g.val p) = h.val (blockOf p) := by
  rcases g with ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨BlockModel.generatorA, blockOf_a⟩
    · exact ⟨BlockModel.generatorB, blockOf_b⟩
  | one => exact ⟨1, fun _ => rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a * b, fun p => (ha (y p)).trans (congrArg a.val (hb p))⟩
  | inv x hx ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨a⁻¹, fun p => ?_⟩
    apply a.val.injective
    simpa using (ha (x⁻¹ p)).symm

private theorem action_unique (g : E) (h k : BlockModel.Model)
    (hh : ∀ p, blockOf (g.val p) = h.val (blockOf p))
    (hk : ∀ p, blockOf (g.val p) = k.val (blockOf p)) : h = k := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  obtain ⟨p, rfl⟩ := blockOf_surjective i
  exact (hh p).symm.trans (hk p)

/-- The action on the literal 65 blocks, with image in their generated group. -/
noncomputable def action : E →* BlockModel.Model where
  toFun g := (exists_action g).choose
  map_one' := action_unique 1 _ 1 (exists_action 1).choose_spec (fun _ => rfl)
  map_mul' g h := action_unique (g * h) _ _ (exists_action (g * h)).choose_spec
    (fun p => ((exists_action g).choose_spec (h.val p)).trans
      (congrArg (exists_action g).choose.val ((exists_action h).choose_spec p)))

theorem action_spec (g : E) (p : Point) :
    blockOf (g.val p) = (action g).val (blockOf p) :=
  (exists_action g).choose_spec p

theorem action_generatorA : action generatorA = BlockModel.generatorA :=
  action_unique generatorA _ _ (action_spec generatorA) blockOf_a

theorem action_generatorB : action generatorB = BlockModel.generatorB :=
  action_unique generatorB _ _ (action_spec generatorB) blockOf_b

theorem action_surjective : Function.Surjective action := by
  rintro ⟨h, hh⟩
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨generatorA, action_generatorA⟩
    · exact ⟨generatorB, action_generatorB⟩
  | one => exact ⟨1, action.map_one⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩
  | inv x hx ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨a⁻¹, by rw [map_inv, ha]; rfl⟩

theorem action_centralZ : action centralZ = 1 := by
  apply action_unique centralZ _ _ (action_spec centralZ)
  intro p
  rw [coe_centralZ]
  exact blockOf_z p

theorem action_centralW : action centralW = 1 := by
  apply action_unique centralW _ _ (action_spec centralW)
  intro p
  rw [coe_centralW]
  exact blockOf_w p

theorem kernel_le_action_ker : kernel ≤ action.ker := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | rfl
  · exact action_centralZ
  · exact action_centralW

/-- The induced, surjective map from the literal central quotient. -/
noncomputable def quotientAction : AtlasModel.Quotient →* BlockModel.Model :=
  QuotientGroup.lift kernel action kernel_le_action_ker

theorem quotientAction_mk (g : E) :
    quotientAction (QuotientGroup.mk g) = action g := by rfl

theorem quotientAction_surjective : Function.Surjective quotientAction := by
  intro h
  obtain ⟨g, rfl⟩ := action_surjective h
  exact ⟨QuotientGroup.mk g, rfl⟩

theorem quotientAction_generatorA :
    quotientAction (QuotientGroup.mk generatorA) = BlockModel.generatorA :=
  action_generatorA

theorem quotientAction_generatorB :
    quotientAction (QuotientGroup.mk generatorB) = BlockModel.generatorB :=
  action_generatorB

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.BlockComparison
