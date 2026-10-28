module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.BlockData

/-!
# The actual action of the covering candidate on its central blocks

Compatibility on the two generators extends by subgroup closure to a
surjective homomorphism onto the degree-252 permutation model. Every displayed
central element fixes the blocks, so the map descends through the literal
quotient `Projective`. The reverse kernel inclusion is proved in `BlockKernel`.
This uses no group-order recognition. Source: Aschbacher–Smith I.1.4(5), p.408;
the ATLAS numerical provenance and action convention are retained in `BlockData`.
The closure construction follows the repository's Suzuki block comparison.
-/

public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.BlockAction

/-- The original involution, now regarded as an element of the covering candidate. -/
def sourceA : Carrier := ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- The original second generator in the covering candidate. -/
def sourceB : Carrier :=
  ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

private theorem exists_action (g : Carrier) :
    ∃ h : Model, ∀ p, blockOf (g.val p) = h.val (blockOf p) := by
  rcases g with ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨generatorA, blockOf_a⟩
    · exact ⟨generatorB, blockOf_b⟩
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

private theorem action_unique (g : Carrier) (h k : Model)
    (hh : ∀ p, blockOf (g.val p) = h.val (blockOf p))
    (hk : ∀ p, blockOf (g.val p) = k.val (blockOf p)) : h = k := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  obtain ⟨p, rfl⟩ := blockOf_surjective i
  exact (hh p).symm.trans (hk p)

/-- The action on the literal 252 central blocks, with image in their generated group. -/
noncomputable def action : Carrier →* Model where
  toFun g := (exists_action g).choose
  map_one' := action_unique 1 _ 1 (exists_action 1).choose_spec (fun _ => rfl)
  map_mul' g h := action_unique (g * h) _ _ (exists_action (g * h)).choose_spec
    (fun p => ((exists_action g).choose_spec (h.val p)).trans
      (congrArg (exists_action g).choose.val ((exists_action h).choose_spec p)))

theorem action_spec (g : Carrier) (p : Point) :
    blockOf (g.val p) = (action g).val (blockOf p) :=
  (exists_action g).choose_spec p

theorem action_generatorA : action sourceA = generatorA :=
  action_unique sourceA _ _ (action_spec sourceA) blockOf_a

theorem action_generatorB : action sourceB = generatorB :=
  action_unique sourceB _ _ (action_spec sourceB) blockOf_b

theorem action_surjective : Function.Surjective action := by
  rintro ⟨h, hh⟩
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨sourceA, action_generatorA⟩
    · exact ⟨sourceB, action_generatorB⟩
  | one => exact ⟨1, action.map_one⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩
  | inv x hx ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨a⁻¹, by rw [map_inv, ha]; rfl⟩

/-- Triviality of the block action means fixation of every displayed block. -/
theorem action_eq_one_iff (g : Carrier) :
    action g = 1 ↔ ∀ p, blockOf (g.val p) = blockOf p := by
  constructor
  · intro h p
    simpa only [h, Subgroup.coe_one, Equiv.Perm.one_apply] using action_spec g p
  · intro h
    exact action_unique g _ 1 (action_spec g) h

private theorem blockOf_pow (z : Perm) (hz : ∀ p, blockOf (z p) = blockOf p)
    (n : ℕ) (p : Point) : blockOf ((z ^ n) p) = blockOf p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hz, ih]

/-- Both independent central coordinates are annihilated by the block action. -/
theorem action_kernelEmbedding (t : KernelCoordinates) : action (kernelEmbedding t) = 1 := by
  apply (action_eq_one_iff _).mpr
  intro p
  rw [kernelEmbedding_val, Equiv.Perm.mul_apply, blockOf_pow z₁ blockOf_z₁,
    blockOf_pow z₂ blockOf_z₂]

theorem centralSubgroup_le_action_ker : centralSubgroup ≤ action.ker := by
  rintro g ⟨t, rfl⟩
  exact action_kernelEmbedding t

/-- The induced map uses exactly the quotient constructed in `Construction`. -/
noncomputable def quotientAction : Projective →* Model :=
  QuotientGroup.lift centralSubgroup action centralSubgroup_le_action_ker

@[simp] theorem quotientAction_mk (g : Carrier) :
    quotientAction (QuotientGroup.mk g) = action g := by rfl

theorem quotientAction_surjective : Function.Surjective quotientAction := by
  intro h
  obtain ⟨g, rfl⟩ := action_surjective h
  exact ⟨QuotientGroup.mk g, rfl⟩

@[simp] theorem quotientAction_sourceA :
    quotientAction (QuotientGroup.mk sourceA) = generatorA := action_generatorA

@[simp] theorem quotientAction_sourceB :
    quotientAction (QuotientGroup.mk sourceB) = generatorB := action_generatorB

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.BlockAction
