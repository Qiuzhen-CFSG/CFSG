/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalCStabilizerBound.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalCScalarNecessity

/-!
# IcosianLocalCStabilizerBound

The shape-C line stabilizer injects into a finite set of permutation and scalar
parameters. Coordinate recovery and candidate counting give the bound.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalCStabilizerBound.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes

/-- The actual lifted monomial stabilizer of the C reference line. -/
def icosianLocalCStabilizer : Subgroup icosianLiftedMonomial :=
  (MulAction.stabilizer icosianHermitianGroup (icosianRootPoint icosianLocalCRoot)).comap
    icosianMonomialToHermitian

def icosianLocalCStabilizerScalar (g : icosianLocalCStabilizer) : icosianNormOneGroup :=
  ((icosianMonomial_line_iff g.val icosianLocalCRoot).mp g.property).choose

theorem icosianLocalCStabilizerScalar_spec (g : icosianLocalCStabilizer) :
    ∀ i,(g.val.val.left i).val.val*(icosianLocalCRoot.val (g.val.val.right.symm i)).val=
      (icosianLocalCRoot.val i).val*(icosianLocalCStabilizerScalar g).val.val :=
  ((icosianMonomial_line_iff g.val icosianLocalCRoot).mp g.property).choose_spec

abbrev IcosianLocalCParameters :=
  {p : Equiv.Perm (Fin 3) // p 0=0} ×
    {v : IcosianIntegerCoordinates // v∈icosianLocalCScalarCandidates}

def icosianLocalCStabilizerParameter (g : icosianLocalCStabilizer) : IcosianLocalCParameters :=
  ⟨⟨g.val.val.right,icosianLocalCLine_permutation g.val g.property⟩,
    ⟨icosianLocalUnitCoordinates (icosianLocalCStabilizerScalar g),
      Finset.mem_filter.mpr ⟨icosianLocalUnitCoordinates_mem _,
        icosianLocalCLine_scalar_test g.val
          (icosianLocalCLine_permutation g.val g.property)
          (icosianLocalCStabilizerScalar g) (icosianLocalCStabilizerScalar_spec g)⟩⟩⟩

theorem icosianLocalCRoot_nonzero (i : Fin 3) : icosianLocalCRoot.val i≠0 := by
  intro hz
  have hn : icosianRootNormWord icosianLocalCRoot i=0 :=
    icosianRootNormWord_of_norm _ _ 0 (by simp [hz,icosianNorm])
  rw [icosianLocalCRoot_word] at hn
  have hne : ∀ j : Fin 3,(if j=0 then (2 : GoldenInteger) else 1)≠0 := by decide +kernel
  exact hne i hn

attribute [local irreducible] icosianLocalCScalarCandidates icosianNormOneCoordinates
set_option backward.isDefEq.respectTransparency true in
theorem icosianLocalCStabilizerParameter_injective :
    Function.Injective icosianLocalCStabilizerParameter := by
  intro g h he
  have hp : g.val.val.right=h.val.val.right :=
    congrArg (fun z : IcosianLocalCParameters => z.1.val) he
  have hc : icosianLocalUnitCoordinates (icosianLocalCStabilizerScalar g)=
      icosianLocalUnitCoordinates (icosianLocalCStabilizerScalar h) :=
    congrArg (fun z : IcosianLocalCParameters => z.2.val) he
  have hu : icosianLocalCStabilizerScalar g=icosianLocalCStabilizerScalar h := by
    apply Subtype.ext
    apply Subtype.ext
    have hq := congrArg icosianCoordinatesQuaternion hc
    simpa only [icosianLocalUnitCoordinates_value] using hq
  apply Subtype.ext
  apply icosianMonomial_line_determined icosianLocalCRoot icosianLocalCRoot_nonzero
    g.val h.val hp (icosianLocalCStabilizerScalar g) (icosianLocalCStabilizerScalar_spec g)
  rw [hu]
  exact icosianLocalCStabilizerScalar_spec h

theorem icosianLocalCParameters_card : Nat.card IcosianLocalCParameters=12 := by
  have hp : Nat.card {p : Equiv.Perm (Fin 3) // p 0=0}=2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [Nat.card_prod,hp,Nat.card_eq_finsetCard,icosianLocalCScalarCandidates_card]

theorem icosianLocalCStabilizer_card_le : Nat.card icosianLocalCStabilizer≤12 := by
  have h := Nat.card_le_card_of_injective icosianLocalCStabilizerParameter
    icosianLocalCStabilizerParameter_injective
  rwa [icosianLocalCParameters_card] at h

end Atlas.Conway
