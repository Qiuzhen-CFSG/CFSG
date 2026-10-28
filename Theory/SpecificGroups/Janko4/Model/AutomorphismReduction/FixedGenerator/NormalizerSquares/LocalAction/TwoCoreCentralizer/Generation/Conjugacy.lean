module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Max2Bridge
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Comparing the original and conjugated max2 subgroups

The certified conjugating word identifies the closure of the original ATLAS
outputs with `localSubgroup` by an actual multiplicative equivalence. The
inclusion of the literal centralizer into `Model` has range exactly C_Model(a).
Consequently a lower bound on the original generated subgroup and a matching
upper bound on the literal centralizer imply full generation.

No centralizer order or maximality is assumed here. Source: the unchanged
`TwoCoreCentralizer/source/J4G1-max2W1`, attributed in `Max2Bridge`; GLS3,
Table 5.3i, printed p.270, motivates the local structure still to be proved.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- The original, unconjugated ATLAS outputs generate this subgroup of the model. -/
def sourceSubgroup : Subgroup Model := Subgroup.closure {w10, w14}

/-- The inclusion of the literal centralizer into the matrix-group carrier. -/
def centralizerToModel : involutionCentralizer →* Model :=
  Subgroup.inclusion involutionCentralizer_le_matrixGroup

theorem centralizerToModel_injective : Function.Injective centralizerToModel :=
  Subgroup.inclusion_injective involutionCentralizer_le_matrixGroup

@[simp] theorem centralizerToModel_localX : centralizerToModel localX = cx := rfl
@[simp] theorem centralizerToModel_localY : centralizerToModel localY = cy := rfl

/-- The centralizer subtype consists exactly of the model elements commuting with a. -/
theorem centralizerToModel_range :
    centralizerToModel.range = Subgroup.centralizer ({a} : Set Model) := by
  ext z
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨c, rfl⟩
    apply toAmbient_injective
    change (c : BinaryMatrixˣ) * matrixUnitA = matrixUnitA * (c : BinaryMatrixˣ)
    exact ((mem_involutionCentralizer_iff _).mp c.property).2
  · intro hz
    refine ⟨⟨toAmbient z, (mem_involutionCentralizer_iff _).mpr ⟨z.property, ?_⟩⟩, rfl⟩
    simpa only [map_mul, toAmbient_a] using congrArg toAmbient hz

/-- Forgetting the centralizer subtype retains exactly the conjugated word subgroup. -/
theorem localSubgroup_map_toModel :
    localSubgroup.map centralizerToModel = Subgroup.closure {cx, cy} := by
  rw [localSubgroup, MonoidHom.map_closure, Set.image_pair,
    centralizerToModel_localX, centralizerToModel_localY]

/-- The conjugacy bridge also identifies the two generated subgroups. -/
theorem sourceSubgroup_map_conj :
    sourceSubgroup.map (MulAut.conj h⁻¹).toMonoidHom =
      localSubgroup.map centralizerToModel := by
  rw [sourceSubgroup, MonoidHom.map_closure, Set.image_pair,
    localSubgroup_map_toModel]
  rfl

/-- The equivalence is actual conjugation on the original ATLAS matrix carrier. -/
noncomputable def sourceSubgroupEquivLocal : sourceSubgroup ≃* localSubgroup :=
  ((MulAut.conj h⁻¹).subgroupMap sourceSubgroup).trans
    ((MulEquiv.subgroupCongr sourceSubgroup_map_conj).trans
      (localSubgroup.equivMapOfInjective centralizerToModel
        centralizerToModel_injective).symm)

@[simp] theorem sourceSubgroupEquivLocal_apply (z : sourceSubgroup) :
    centralizerToModel (sourceSubgroupEquivLocal z) = h⁻¹ * (z : Model) * h := by
  have he := (localSubgroup.equivMapOfInjective centralizerToModel
    centralizerToModel_injective).apply_symm_apply
      ((MulEquiv.subgroupCongr sourceSubgroup_map_conj)
        ((MulAut.conj h⁻¹).subgroupMap sourceSubgroup z))
  have he' := congrArg (fun x : localSubgroup.map centralizerToModel => (x : Model)) he
  change centralizerToModel (sourceSubgroupEquivLocal z) =
    h⁻¹ * (z : Model) * (h⁻¹)⁻¹ at he'
  simpa only [inv_inv] using he'

theorem card_sourceSubgroup_eq_localSubgroup :
    Nat.card sourceSubgroup = Nat.card localSubgroup :=
  Nat.card_congr sourceSubgroupEquivLocal.toEquiv

/-- Matching bounds for a subgroup and its finite ambient group force generation. -/
theorem localSubgroup_eq_top_of_card_bounds {n : ℕ}
    (hlower : n ≤ Nat.card sourceSubgroup)
    (hupper : Nat.card involutionCentralizer ≤ n) : localSubgroup = ⊤ := by
  apply localSubgroup.eq_top_of_card_eq
  exact le_antisymm localSubgroup.card_le_card_group
    (hupper.trans (hlower.trans_eq card_sourceSubgroup_eq_localSubgroup))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
