module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.ModelComponents.Common
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.ModelComponents.Permutation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.ModelComponents.Linear
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Simple components and natural sections of the G.6.4 actor models

A nonsolvable concrete actor has a simple perfect normal subgroup: the whole
linear actor in dimension at least three, or the actual alternating subgroup
in the symmetric alternatives. The two-dimensional linear actor is excluded
by solvability. In each case the literal displacement quotient by its fixed
vectors is identified equivariantly with the specified natural module.

The permutation-core cases use the actual `coreToNatural` map, its fixed-vector
kernel and commutator generation. All identifications are transported through
the group and module equivalences supplied by `ActorModel`; no recognition,
simplicity or section-identification premise is added.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.6.4(2),
printed pp.345–346, and the first paragraph of 13.8.5, printed p.947.
This proves the intrinsic model step; the parent constructs `ActorModel` and
performs the source-group lifting.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep.ModelComponents
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- The whole nonsolvable linear actor gives the natural linear component. -/
theorem linear_component (ρ : Representation (ZMod 2) A E) (hns : ¬ Group.IsSolvable A)
    (n : ℕ) (hn : 2 ≤ n) (hn5 : n ≤ 5) (hm : HasActionModel ρ (linearRepresentation n)) :
    ∃ C : Subgroup A, C.Normal ∧ IsSimpleGroup C ∧ Group.IsPerfect C ∧
      ¬ IsMulCommutative C ∧ NaturalSection ρ C := by
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2 : n = 2 := by omega
    subst n
    obtain ⟨eA, _, _⟩ := hm
    let : Group.IsSolvable (BinaryLinear.OuterCyclic.LinearGroup 2) := linear_two_solvable
    exact hns (Group.isSolvable_of_isSolvable_injective (f := eA.toMonoidHom) eA.injective)
  let B := BinaryLinear.OuterCyclic.LinearGroup n
  let : IsSimpleGroup B := linear_simple n hn3
  let : Group.IsPerfect B := BinaryLinear.linearGroup_isPerfect n hn3
  let : IsSimpleGroup (⊤ : Subgroup B) := Subgroup.topEquiv.isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup B) := Group.IsPerfect.ofSurjective
    (f := (Subgroup.topEquiv (G := B)).symm.toMonoidHom) Subgroup.topEquiv.symm.surjective
  obtain ⟨C, hC, hs, hp, hc, eC, heC⟩ := component_of_model ρ
    (linearRepresentation n) (linearRepresentation n) hm (⊤ : Subgroup B)
    Subgroup.topEquiv (LinearMap.id) Function.surjective_id
    (linear_generated n hn) (by rw [LinearMap.ker_id, linear_fixed n hn])
    (fun _ _ => rfl)
  exact ⟨C, hC, hs, hp, hc, Or.inl ⟨n, hn3, hn5, eC, heC⟩⟩

/-- The actual alternating subgroup supplies the natural symmetric-model section. -/
theorem natural_component (ρ : Representation (ZMod 2) A E)
    (n : ℕ) (hn : 5 ≤ n) (hn8 : n ≤ 8)
    (hm : HasActionModel ρ (BinaryPermutation.naturalRepresentation (Fin n))) :
    ∃ C : Subgroup A, C.Normal ∧ IsSimpleGroup C ∧ Group.IsPerfect C ∧
      ¬ IsMulCommutative C ∧ NaturalSection ρ C := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  let : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
  obtain ⟨C, hC, hs, hp, hc, eC, heC⟩ := component_of_model ρ
    (BinaryPermutation.naturalRepresentation (Fin n))
    (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) hm (alternatingGroup (Fin n))
    (MulEquiv.refl _) (LinearMap.id) Function.surjective_id
    (natural_generated n hn) (by rw [LinearMap.ker_id, natural_fixed n hn])
    (fun _ _ => rfl)
  exact ⟨C, hC, hs, hp, hc, Or.inr ⟨n, hn, hn8, eC, heC⟩⟩

/-- On the permutation core the quotient is given by the actual core projection. -/
theorem core_component (ρ : Representation (ZMod 2) A E)
    (n : ℕ) (hn : n = 6 ∨ n = 8)
    (hm : HasActionModel ρ (BinaryPermutation.coreRepresentation (Fin n))) :
    ∃ C : Subgroup A, C.Normal ∧ IsSimpleGroup C ∧ Group.IsPerfect C ∧
      ¬ IsMulCommutative C ∧ NaturalSection ρ C := by
  have hn5 : 5 ≤ n := by omega
  have hn8 : n ≤ 8 := by omega
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn5)
  let : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa using hn5)⟩
  obtain ⟨C, hC, hs, hp, hc, eC, heC⟩ := component_of_model ρ
    (BinaryPermutation.coreRepresentation (Fin n))
    (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) hm (alternatingGroup (Fin n))
    (MulEquiv.refl _) (BinaryPermutation.coreToNatural (Fin n))
    BinaryPermutation.coreToNatural_surjective (core_generated n hn5) (core_projection_kernel n hn5)
    (fun g v => BinaryPermutation.coreToNatural_equivariant g.val v)
  exact ⟨C, hC, hs, hp, hc, Or.inr ⟨n, hn5, hn8, eC, heC⟩⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep.ModelComponents

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
open scoped IsMulCommutative
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- Each nonsolvable G.6.4 actor has a simple perfect normal component on whose
literal commutator quotient the action is the specified natural model. -/
theorem exists_simple_normal_naturalSection (ρ : Representation (ZMod 2) A E)
    (hns : ¬ Group.IsSolvable A) (hm : ActorModel ρ) :
    ∃ C : Subgroup A, C.Normal ∧ IsSimpleGroup C ∧ Group.IsPerfect C ∧
      ¬ IsMulCommutative C ∧ NaturalSection ρ C := by
  rcases hm with ⟨n, hn, hn5, hm⟩ | ⟨n, hn, hn8, hm⟩ | ⟨n, hn, hm⟩
  · exact ModelComponents.linear_component ρ hns n hn hn5 hm
  · exact ModelComponents.natural_component ρ n hn hn8 hm
  · exact ModelComponents.core_component ρ n hn hm
end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

end
