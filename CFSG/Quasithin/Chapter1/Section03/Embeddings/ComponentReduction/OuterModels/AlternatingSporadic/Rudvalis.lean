module

public import Theory.GroupAction.AutomorphismNormalizer
public import Theory.GroupTheory.CyclicNormalOddQuotient
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.Rudvalis.Model.Primitive
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Triviality of the Rudvalis outer group

The Rudvalis entry in GLS3, Table 5.3r (printed p.279), states `Out(Ru) = 1`.
Theorem C of Aschbacher–Smith (combined 1 March 2004 manuscript, printed p.33)
includes Ru, whose outer group is inspected in the proof of 1.3.4 on p.510.

For the fixed degree-4060 model, two concrete action facts suffice: abstract
automorphisms preserve the class of point stabilizers, and the permutation
normalizer is the model subgroup itself. The orbit–stabilizer construction
then realizes each automorphism by an element of the model. This makes the
actual quotient `Aut(Ru)/Inn(Ru)` trivial, and an actual model isomorphism
transports the requested cyclic-normal odd-quotient restriction.

The concrete normalizer and stabilizer-class theorems discharge both action
premises in the final exports. The latter uses simplicity, transported from
the supplied group along its actual model isomorphism. The conditional APIs
are retained. Triviality also supplies the full outer-solvability input used
by the companion inspection in `OuterModels.Solvability`.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels

open Theory.GroupTheory

/-- Conditional realization of all Rudvalis automorphisms by conjugation.
The class of the point stabilizer and the permutation normalizer both require
concrete proofs; neither follows just from the checked generator relations. -/
theorem rudvalis_conj_surjective_of_action
    (hstable : ∀ f : MulAut Rudvalis.Model, ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y)
    (hnormalizer : Subgroup.normalizer
      (Rudvalis.modelSubgroup : Set (Equiv.Perm (Fin 4060))) = Rudvalis.modelSubgroup) :
    Function.Surjective (MulAut.conj : Rudvalis.Model →* MulAut Rudvalis.Model) := by
  let : MulAction.IsPretransitive Rudvalis.modelSubgroup (Fin 4060) :=
    Rudvalis.model_isPretransitive
  exact Subgroup.conj_surjective_of_stabilizers_of_normalizer
    Rudvalis.modelSubgroup 0 hstable hnormalizer

/-- The two action calculations would make the actual outer quotient trivial. -/
theorem rudvalis_outer_subsingleton_of_action
    (hstable : ∀ f : MulAut Rudvalis.Model, ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y)
    (hnormalizer : Subgroup.normalizer
      (Rudvalis.modelSubgroup : Set (Equiv.Perm (Fin 4060))) = Rudvalis.modelSubgroup) :
    Subsingleton (MulAut.Outer Rudvalis.Model) := by
  apply QuotientGroup.subsingleton_iff.mpr
  exact MonoidHom.range_eq_top.mpr
    (rudvalis_conj_surjective_of_action hstable hnormalizer)

/-- Conditional outer restriction for a group actually isomorphic to the fixed
Rudvalis model. Final assembly must supply both concrete action calculations. -/
theorem rudvalis_model_outer_cyclicNormalOddQuotient_of_action
    {S : Type*} [Group S] (e : S ≃* Rudvalis.Model)
    (hstable : ∀ f : MulAut Rudvalis.Model, ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y)
    (hnormalizer : Subgroup.normalizer
      (Rudvalis.modelSubgroup : Set (Equiv.Perm (Fin 4060))) = Rudvalis.modelSubgroup) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  let := rudvalis_outer_subsingleton_of_action hstable hnormalizer
  exact (hasCyclicNormalOddQuotient_of_isCyclic (G := MulAut.Outer Rudvalis.Model)).of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- Every automorphism of the simple Rudvalis carrier is inner: the concrete
stabilizer-class and permutation-normalizer calculations realize it by conjugation. -/
theorem rudvalis_conj_surjective [IsSimpleGroup Rudvalis.Model] :
    Function.Surjective (MulAut.conj : Rudvalis.Model →* MulAut Rudvalis.Model) :=
  rudvalis_conj_surjective_of_action Rudvalis.outer_stabilizer_map_eq
    Rudvalis.outer_permutation_normalizer_eq

/-- The actual quotient `Aut(Ru)/Inn(Ru)` is trivial, as in GLS3 Table 5.3r. -/
theorem rudvalis_outer_subsingleton [IsSimpleGroup Rudvalis.Model] :
    Subsingleton (MulAut.Outer Rudvalis.Model) :=
  rudvalis_outer_subsingleton_of_action Rudvalis.outer_stabilizer_map_eq
    Rudvalis.outer_permutation_normalizer_eq

/-- The full Rudvalis outer-solvability input for the companion Theorem C inspection. -/
theorem rudvalis_outer_isSolvable [IsSimpleGroup Rudvalis.Model] :
    Group.IsSolvable (MulAut.Outer Rudvalis.Model) := by
  let := rudvalis_outer_subsingleton
  infer_instance

/-- The Rudvalis case of the source outer restriction, transported through the
actual model isomorphism with both concrete action premises discharged. -/
theorem rudvalis_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (e : S ≃* Rudvalis.Model) : HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  exact rudvalis_model_outer_cyclicNormalOddQuotient_of_action e
    Rudvalis.outer_stabilizer_map_eq Rudvalis.outer_permutation_normalizer_eq

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
