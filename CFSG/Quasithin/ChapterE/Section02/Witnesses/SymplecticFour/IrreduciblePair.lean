module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.Geometry
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.PGroupCore

/-!
# The original Sp4 opposite pair has no normal two-subgroup

Apply the concrete central-root calculation to V inside the literal Sylow
center. The action stays on the original F-four-space and the group is exactly
〈V,V^w〉. Its faithful irreducibility kills its two-core by the modular fixed
vector theorem. This supplies the actual input to both recognition branches
in the proof of E.2.7, printed pp.219–221; no subgroup model is assumed here.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open TwoConjugate
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem pairAction_faithful (V : Subgroup (Sp F)) :
    Function.Injective (pairAction V) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun f : Module.End F (Vector F) => f (Pi.single j 1) i) he
  change ((g : Sp F).val *ᵥ Pi.single j 1) i =
    ((h : Sp F).val *ᵥ Pi.single j 1) i at hh
  simpa using hh

/-- The literal non-diagonal E.2.7 pair is F-irreducible and has trivial
O₂. All central and root markings refer to the actual standard Sylow. -/
theorem source_pair_irreducible_and_twoCore (V : Subgroup (Sp F))
    (hc : V ≤ (center (unipotent (F := F))).map (unipotent (F := F)).subtype)
    (hl : ¬V ≤ RootSubgroup.group 0) (hs : ¬V ≤ RootSubgroup.group 4)
    (hd : ∀μ:F,μ≠0 → ¬V ≤ diagonal μ) :
    Representation.IsIrreducible (pairAction V) ∧ pCore 2 (oppositePair V) = ⊥ := by
  have hi := pairAction_irreducible_of_no_diagonal V
    (CentralRootGeometry.parameter_range (F := F) ▸ hc) hl hs hd
  let := hi
  refine ⟨hi,?_⟩
  have hk := Representation.normal_p_subgroup_le_ker (pairAction V)
    (pCore 2 (oppositePair V)) pCore_isPGroup
  exact le_bot_iff.mp (hk.trans ((MonoidHom.ker_eq_bot_iff _).mpr (pairAction_faithful V)).le)

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
