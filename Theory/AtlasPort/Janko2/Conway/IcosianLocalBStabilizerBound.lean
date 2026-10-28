/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalBStabilizerBound.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalBReference

/-!
# IcosianLocalBStabilizerBound

A shape-B line stabilizer injects into explicit permutation and scalar parameters.
Counting those parameters bounds the stabilizer.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalBStabilizerBound.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes
open scoped Matrix

def icosianLocalBStabilizer : Subgroup icosianLiftedMonomial :=
  (MulAction.stabilizer icosianHermitianGroup (icosianRootPoint icosianLocalBRoot)).comap
    icosianMonomialToHermitian

theorem icosianLocalBStabilizer_blocks (g : icosianLocalBStabilizer) :
    ∃ ha : (icosianNormOneReduction (g.val.val.left 1)) 1 0=0,
      icosianNormOneReduction (g.val.val.left 0)=
        icosianUpperDiagonal ⟨icosianNormOneReduction (g.val.val.left 1),ha⟩ := by
  have hr := icosianLocalBLine_repeated g.val g.property
  have hg := g.val.property
  change icosianMonomialReduction g.val.val∈icosianGlueMonomialStabilizer GoldenFour at hg
  rw [icosianGlueMonomialStabilizer_iff] at hg
  change IcosianGluePreserves (fun i => icosianNormOneReduction (g.val.val.left i)) at hg
  have he : (fun i => icosianNormOneReduction (g.val.val.left i))=
      ![icosianNormOneReduction (g.val.val.left 0),icosianNormOneReduction (g.val.val.left 1),
        icosianNormOneReduction (g.val.val.left 1)] := by
    funext i
    fin_cases i <;> simp [hr]
  rw [he] at hg
  have htwo (x : GoldenFour) : x+x=0 := by ext <;> simp [CharTwo.add_self_eq_zero]
  obtain ⟨ha,h00,h11,h10,h01⟩ :=
    (icosianGlue_repeated_blocks_iff htwo _ _).mp hg
  refine ⟨ha,?_⟩
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [icosianUpperDiagonal,h00,h11,h10,h01]

abbrev IcosianLocalBParameters :=
  {p : Equiv.Perm (Fin 3) // p 0=0} × IcosianRepeatedUnitParameters

def icosianLocalBStabilizerParameter (g : icosianLocalBStabilizer) : IcosianLocalBParameters :=
  ⟨⟨g.val.val.right,icosianLocalBLine_permutation g.val g.property⟩,
    ⟨⟨g.val.val.left 1,(icosianLocalBStabilizer_blocks g).choose⟩,
      ⟨g.val.val.left 0,(icosianLocalBStabilizer_blocks g).choose_spec⟩⟩⟩

theorem icosianLocalBStabilizerParameter_injective :
    Function.Injective icosianLocalBStabilizerParameter := by
  intro g h he
  have hp : g.val.val.right=h.val.val.right :=
    congrArg (fun p : IcosianLocalBParameters => p.1.val) he
  have h1 : g.val.val.left 1=h.val.val.left 1 :=
    congrArg (fun p : IcosianLocalBParameters => p.2.1.val) he
  have h0 : g.val.val.left 0=h.val.val.left 0 :=
    congrArg (fun p : IcosianLocalBParameters => p.2.2.val) he
  apply Subtype.ext
  apply Subtype.ext
  apply SemidirectProduct.ext
  · funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact (icosianLocalBLine_repeated g.val g.property).symm.trans
        (h1.trans (icosianLocalBLine_repeated h.val h.property))
  · exact hp

theorem icosianLocalBParameters_card : Nat.card IcosianLocalBParameters=96 := by
  have hp : Nat.card {p : Equiv.Perm (Fin 3) // p 0=0}=2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [Nat.card_prod,hp,icosianRepeatedUnitParameters_card]

theorem icosianLocalBStabilizer_card_le : Nat.card icosianLocalBStabilizer≤96 := by
  have h := Nat.card_le_card_of_injective icosianLocalBStabilizerParameter
    icosianLocalBStabilizerParameter_injective
  rwa [icosianLocalBParameters_card] at h

end Atlas.Conway
