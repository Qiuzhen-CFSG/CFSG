/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/LeechCrossKernel.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.LeechCentralQuotient
public import Theory.AtlasPort.OtherSporadic.Conway.MonomialStabilizer
public import Theory.AtlasPort.OtherSporadic.Conway.TetradParityConstant
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetFaithful
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSextetPermutations
/-!
Central signs, antipodal geometry, and faithful quotient actions for the Leech isometry group.
The proofs identify the actual kernels and transport the concrete actions through the central quotient.

Source: Gerald Höhn, `Atlas/Conway/LeechCrossKernel.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem crossAction_mul (g h : LeechIsometryGroup) (X : LeechCross) :
    crossAction (g*h) X = crossAction g (crossAction h X) := by
  exact congrArg (fun p : Equiv.Perm LeechCross => p X) (crossRepresentation.map_mul g h)

theorem monomial_factor (m : GolayMonomialGroup) :
    monomialEmbedding m = signIsometry m.left.toAdd * permutationIsometry m.right := rfl

theorem monomial_permutation_eq_one_of_fixes_crosses (m : GolayMonomialGroup)
    (hm : ∀ X, crossAction (monomialEmbedding m) X = X) : m.right = 1 := by
  apply mathieu_eq_one_of_fixes_sextets
  intro S
  have he := hm (sextetCross S 0)
  rw [monomial_factor,crossAction_mul,sextetCross_permutation_action] at he
  rw [sextetCross_sign_action _ _ _ (sextetBaseParameter (sextetAction m.right S) 0).1] at he
  exact congrArg Prod.fst (sextetCross_injective (a₁ := (sextetAction m.right S, _)) (a₂ := (S, 0)) he)

theorem sign_parity_zero_of_fixes_crosses (c : golay)
    (hc : ∀ X, crossAction (signIsometry c) X = X)
    (T : Finset Omega) (hT : T.card = 4) : tetradSignParity c.val T = 0 := by
  let S := sextetCompletion ⟨T,hT⟩
  have he := hc (sextetCross S 0)
  rw [sextetCross_sign_action S 0 c ⟨T,tetrad_mem_completion ⟨T,hT⟩⟩] at he
  have hp := congrArg Prod.snd (sextetCross_injective (a₁ := (S, 0 + tetradSignParity c.val T)) (a₂ := (S, 0)) he)
  simpa using hp

theorem sign_eq_one_or_negation_of_fixes_crosses (c : golay)
    (hc : ∀ X, crossAction (signIsometry c) X = X) :
    signIsometry c = 1 ∨ signIsometry c = negationIsometry := by
  have he := constant_of_tetrad_parity c.val (sign_parity_zero_of_fixes_crosses c hc)
  let a : Omega := ((0,0),0)
  rcases bit_cases (c.val a) with hz | ho
  · left
    apply Subtype.ext; apply LinearEquiv.ext; intro x; apply Subtype.ext; ext i
    change signChange c.val x.val i = x.val i
    simp [signChange,he i a,hz]
  · right
    apply Subtype.ext; apply LinearEquiv.ext; intro x; apply Subtype.ext; ext i
    change signChange c.val x.val i = -x.val i
    simp [signChange,he i a,ho]

theorem fixes_crosses_eq_one_or_negation (g : LeechIsometryGroup)
    (hg : ∀ X, crossAction g X = X) : g = 1 ∨ g = negationIsometry := by
  let m := recoverMonomial g (hg standardCross)
  have hm : monomialEmbedding m = g := recoverMonomial_spec _ _
  have hf : ∀ X, crossAction (monomialEmbedding m) X = X := by simpa [hm] using hg
  have hp := monomial_permutation_eq_one_of_fixes_crosses m hf
  have hs : monomialEmbedding m = signIsometry m.left.toAdd := by
    rw [monomial_factor,hp]
    change signIsometry m.left.toAdd * permutationEmbedding 1 = _
    rw [map_one,mul_one]
  rw [← hm,hs]
  apply sign_eq_one_or_negation_of_fixes_crosses
  simpa [hs] using hf

theorem negation_modTwo_trivial : leechModTwoRepresentation negationIsometry = 1 := by
  apply LinearEquiv.ext; intro a
  obtain ⟨x,rfl⟩ := leechReduction_surjective a
  rw [leechModTwoRepresentation_reduce,negationIsometry_apply,leechReduction_neg]
  rfl

theorem negation_fixes_crosses (X : LeechCross) : crossAction negationIsometry X = X := by
  apply Subtype.ext
  change leechModTwoRepresentation negationIsometry X.val = X.val
  rw [negation_modTwo_trivial]
  rfl

theorem crossRepresentation_kernel : crossRepresentation.ker = leechCentralSigns := by
  ext g
  rw [leechCentralSigns_mem]
  constructor
  · intro hg
    apply fixes_crosses_eq_one_or_negation
    intro X
    exact congrArg (fun p : Equiv.Perm LeechCross => p X) (MonoidHom.mem_ker.mp hg)
  · rintro (rfl | rfl)
    · exact crossRepresentation.ker.one_mem
    · apply MonoidHom.mem_ker.mpr
      apply Equiv.ext; intro X
      exact negation_fixes_crosses X

theorem leechModTwoRepresentation_kernel : leechModTwoRepresentation.ker = leechCentralSigns := by
  ext g
  rw [leechCentralSigns_mem]
  constructor
  · intro hg
    apply fixes_crosses_eq_one_or_negation
    intro X
    apply Subtype.ext
    change leechModTwoRepresentation g X.val = X.val
    rw [MonoidHom.mem_ker.mp hg]
    rfl
  · rintro (rfl | rfl)
    · exact leechModTwoRepresentation.ker.one_mem
    · exact MonoidHom.mem_ker.mpr negation_modTwo_trivial

end Atlas.Conway
