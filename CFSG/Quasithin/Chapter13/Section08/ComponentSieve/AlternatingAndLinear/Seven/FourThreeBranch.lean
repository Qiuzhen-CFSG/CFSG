module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.ConjugateObstruction
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic

/-!
# The four-plus-three branch of the seven-point sieve

This file preserves the preliminary conditional interface for the first
partition in the proof of Aschbacher--Smith 13.8.24. The action and intrinsic
two-core are literal, and the final parity obstruction is proved. The records
below still assume the natural-module selection, quadratic rank bound and
critical-pair transvection. They do not prove those source deductions.

In particular, the legacy `HasFourDualModel` is the six-dimensional deleted
permutation module plus its dual, of dimension twelve. It is not the source's
four-plus-dual alternative. The correct four-dimensional component models are
`PairsBranch.ModuleSelection.IsFour` and `IsFourPlusDual`. The legacy public
interfaces are retained for compatibility and must not certify 13.8.24.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
13.8.13, 13.8.18, 13.8.21--24, printed pp.953--959 (1 March 2004).
-/

@[expose] public section

open Equiv Subgroup BinaryPermutation Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven

/-! ## The solvable four-point stabilizer -/

private theorem symmetric_three_isSolvable :
    Group.IsSolvable (Perm (Fin 3)) := by
  let : Group.IsSolvable (Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let e := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (by decide : 3 ≤ 4))
  exact Group.isSolvable_of_isSolvable_injective (f := e)
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))

/-- The actual `S₄ × S₃` partition stabilizer is solvable. -/
theorem fourThreeStabilizer_isSolvable :
    Group.IsSolvable fourThreeStabilizer := by
  let : Group.IsSolvable (Perm (Fin 3)) := symmetric_three_isSolvable
  let : Group.IsSolvable (Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable FourThree := inferInstance
  exact Group.isSolvable_of_isSolvable_injective
    (f := fourThreeEquiv.symm.toMonoidHom) fourThreeEquiv.symm.injective

/-- Solvability transported to the actual preimage of the partition
stabilizer.  The equality is an equality of subgroup images, so this does not
silently identify an arbitrary subgroup with a model copy. -/
theorem solvable_of_fourThree_image {H : Type*} [Group H]
    (φ : H →* S7) (hφ : Function.Injective φ) (P : Subgroup H)
    (hP : P.map φ = fourThreeStabilizer) : Group.IsSolvable P := by
  let : Group.IsSolvable fourThreeStabilizer := fourThreeStabilizer_isSolvable
  let e : P ≃* fourThreeStabilizer :=
    (P.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hP)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-! ## The relative four-point stabilizer -/

/-- The equality with `H ∩ M` is the maximality step used after the
solvability calculation.  Both containments are retained explicitly: the
first is the fact that the four-point stabilizer lies in the maximal local,
and the second is the needed maximality conclusion. -/
theorem fourPointStabilizer_eq_inter {H : Type*} [Group H]
    (P M : Subgroup H) (hPM : P ≤ M)
    (hmax : (⊤ : Subgroup H) ⊓ M ≤ P) :
    P = (⊤ : Subgroup H) ⊓ M := by
  apply le_antisymm
  · exact le_inf le_top hPM
  · exact hmax

/-! ## The two model alternatives -/

/-- Legacy natural-plus-dual model of dimension twelve. This is not the
four-plus-dual alternative in B.4 or 13.8.24. Its action is nevertheless literal. -/
def HasFourDualModel {H E : Type*} [Group H] [AddCommGroup E]
    [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (φ : H →* S7) : Prop :=
  ∃ e : E ≃ₗ[ZMod 2]
      (core (Fin 7) × Module.Dual (ZMod 2) (core (Fin 7))),
    ∀ g v,
      e (ρ g v) =
        (coreRepresentation (Fin 7) (φ g) (e v).1,
          (coreRepresentation (Fin 7) (φ g⁻¹)).dualMap (e v).2)

/-- The legacy model has dimension twelve, so it cannot encode the
four-plus-dual alternative of the source. -/
theorem hasFourDualModel_finrank {H E : Type*} [Group H] [AddCommGroup E]
    [Module (ZMod 2) E] (ρ : Representation (ZMod 2) H E) (φ : H →* S7)
    (h : HasFourDualModel ρ φ) : Module.finrank (ZMod 2) E = 12 := by
  obtain ⟨e, _⟩ := h
  rw [e.finrank_eq, Module.finrank_prod, Subspace.dual_finrank_eq,
    BinaryPermutation.finrank_core]
  decide

/-- Eliminate the legacy twelve-dimensional alternative from an explicit disjunction.
This does not select the natural module from the actual B.4 alternatives. -/
theorem natural_of_model_alternatives {H E : Type*} [Group H]
    [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (φ : H →* S7)
    (haltern : HasNaturalSubmodule ρ φ ∨ HasFourDualModel ρ φ)
    (hdual : ¬ HasFourDualModel ρ φ) : HasNaturalSubmodule ρ φ := by
  rcases haltern with h | h
  · exact h
  · exact (hdual h).elim

/-! ## The numerical and critical-pair transfers -/

/-- The quadratic rank calculation in the actual two-core gives multiplicity
one.  The two inequalities are the source outputs: positivity records that
the actor is nontrivial, while the upper bound is the quadratic calculation on
the selected natural module. -/
theorem multiplicity_eq_one_of_quadratic (m : ℕ) (hpos : 0 < m)
    (hquad : m ≤ 1) : m = 1 := by omega

/-! ## Final branch data and contradiction -/

structure FourThreeBranchData {H E : Type*} [Group H] [Finite H]
    [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) where
  φ : H →* S7
  hφ : Function.Injective φ
  P : Subgroup H
  hP : P.map φ = fourThreeStabilizer
  A : Subgroup H
  V : Subgroup H
  hA : IsElementaryTwo A
  hAV : A ≤ V
  y : H
  hplace : V.map (MulAut.conj y).toMonoidHom ≤
    (pCore 2 P).map P.subtype
  ht : ∃ a ∈ A, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1

/-- The four-plus-three branch contradiction for a faithful compatible
seven-point action. -/
theorem fourThree_branch_contradiction {H E : Type*} [Group H] [Finite H]
    [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E)
    (d : FourThreeBranchData ρ)
    (hmodel : HasNaturalSubmodule ρ d.φ) : False := by
  exact no_conjugated_transvection_in_fourThreeCore ρ d.φ d.hφ hmodel d.P d.A d.V
    d.hP d.hA d.hAV d.y d.hplace d.ht

/-! ## The source assembly interface -/

/-- Preliminary conditional record, not an encoding of case (2) of 13.8.8. The fields named
`hdual`, `hquad`, and `ht` are precisely the three non-formal obligations in
the printed argument: the rank-two calculation excludes four-plus-dual,
quadraticity forces `m(Vα*) = 1`, and 13.8.18(3) transports a transvection to
the conjugated `Vβ` actor. -/
structure FourThreeSourceInput {H E : Type*} [Group H] [Finite H]
    [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) extends FourThreeBranchData ρ where
  M : Subgroup H
  hPM : P ≤ M
  hmax : (⊤ : Subgroup H) ⊓ M ≤ P
  mVα : ℕ
  hmVα_pos : 0 < mVα
  hmVα_quad : mVα ≤ 1
  haltern : HasNaturalSubmodule ρ φ ∨ HasFourDualModel ρ φ
  hdual : ¬ HasFourDualModel ρ φ

/-- All structural consequences needed before the parity endpoint. -/
theorem fourThree_source_structure {H E : Type*} [Group H] [Finite H]
    [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E)
    (d : FourThreeSourceInput ρ) :
    Group.IsSolvable d.P ∧ d.P = (⊤ : Subgroup H) ⊓ d.M ∧ d.mVα = 1 ∧
      HasNaturalSubmodule ρ d.φ := by
  refine ⟨solvable_of_fourThree_image d.φ d.hφ d.P d.hP,
    fourPointStabilizer_eq_inter d.P d.M d.hPM d.hmax,
    multiplicity_eq_one_of_quadratic d.mVα d.hmVα_pos d.hmVα_quad,
    natural_of_model_alternatives ρ d.φ d.haltern d.hdual⟩

/-- Conditional parity endpoint. Its record still contains unproved source obligations. -/
theorem exclude_fourThree_partition {H E : Type*} [Group H] [Finite H]
    [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E)
    (d : FourThreeSourceInput ρ) : False := by
  have hmodel := natural_of_model_alternatives ρ d.φ d.haltern d.hdual
  exact no_conjugated_transvection_in_fourThreeCore ρ d.φ d.hφ hmodel d.P d.A d.V
    d.hP d.hA d.hAV d.y d.hplace d.ht

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven

end
