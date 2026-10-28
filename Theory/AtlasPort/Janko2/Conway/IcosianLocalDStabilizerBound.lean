/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalDStabilizerBound.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalDReductionNecessity

/-!
# IcosianLocalDStabilizerBound

The shape-D line stabilizer injects into the parameters satisfying its reduction
test. This injection gives the stabilizer bound used in orbit exhaustion.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalDStabilizerBound.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes

def icosianLocalDStabilizer : Subgroup icosianLiftedMonomial :=
  (MulAction.stabilizer icosianHermitianGroup (icosianRootPoint icosianLocalDRoot)).comap
    icosianMonomialToHermitian

def icosianLocalDStabilizerScalar (g : icosianLocalDStabilizer) : icosianNormOneGroup :=
  ((icosianMonomial_line_iff g.val icosianLocalDRoot).mp g.property).choose

theorem icosianLocalDStabilizerScalar_spec (g : icosianLocalDStabilizer) :
    ∀ i,(g.val.val.left i).val.val*(icosianLocalDRoot.val (g.val.val.right.symm i)).val=
      (icosianLocalDRoot.val i).val*(icosianLocalDStabilizerScalar g).val.val :=
  ((icosianMonomial_line_iff g.val icosianLocalDRoot).mp g.property).choose_spec

def icosianLocalDStabilizerParameter (g : icosianLocalDStabilizer) : IcosianLocalDUnitParameters :=
  ⟨icosianLocalDStabilizerScalar g,
    icosianLocalDLine_reduction_test g.val (icosianLocalDLine_permutation g.val g.property)
      (icosianLocalDStabilizerScalar g) (icosianLocalDStabilizerScalar_spec g)⟩

theorem icosianLocalDStabilizerParameter_injective :
    Function.Injective icosianLocalDStabilizerParameter := by
  intro g h he
  have hp : g.val.val.right=h.val.val.right :=
    (icosianLocalDLine_permutation g.val g.property).trans
      (icosianLocalDLine_permutation h.val h.property).symm
  have hu : icosianLocalDStabilizerScalar g=icosianLocalDStabilizerScalar h :=
    congrArg (fun p : IcosianLocalDUnitParameters => p.val) he
  apply Subtype.ext
  apply icosianMonomial_line_determined icosianLocalDRoot icosianLocalDRoot_nonzero
    g.val h.val hp (icosianLocalDStabilizerScalar g) (icosianLocalDStabilizerScalar_spec g)
  rw [hu]
  exact icosianLocalDStabilizerScalar_spec h

theorem icosianLocalDStabilizer_card_le : Nat.card icosianLocalDStabilizer≤24 := by
  have h := Nat.card_le_card_of_injective icosianLocalDStabilizerParameter
    icosianLocalDStabilizerParameter_injective
  rwa [icosianLocalDUnitParameters_card] at h

end Atlas.Conway
