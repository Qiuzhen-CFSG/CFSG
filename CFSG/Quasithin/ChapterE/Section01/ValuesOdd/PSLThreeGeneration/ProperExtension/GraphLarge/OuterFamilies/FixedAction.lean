module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.ActorGeometry
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph.Equivalence
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.GraphLargeStructure.Action

/-!
# The actual action of an outer involution on the inner actor

Conjugation identifies the marked inner subgroup with PSL₃. Since an elementary
actor commutes with each of its elements, its inner intersection embeds in the
literal fixed subgroup of a selected outer involution. The checked graph-fixed
calculation identifies this entire fixed subgroup with an actual ternary special
orthogonal group over the original field.

This supplies the action input for E.1.14(7), printed p.214, with GLS3 §§2.7
and 4.3 for the fixed-group calculation. Neither E-membership nor a Sylow claim
follows just from this embedding; those local construction obligations remain.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

omit [Finite F] in
/-- Embed the actual inner intersection in the fixed subgroup of the chosen actor element. -/
theorem actor_inner_fixed_embedding
    (A : Subgroup (graphExtension F)) [IsElementaryAbelian 2 A]
    (t : graphExtension F) (ht : t ∈ A) :
    ∃ f : (A ⊓ innerPart F : Subgroup _) →* (t : MulAut PSL(3,F)).fixedSubgroup,
      Function.Injective f := by
  let f : (A ⊓ innerPart F : Subgroup _) →*
      (centralizer ({t} : Set (graphExtension F))).subgroupOf (innerPart F) := {
    toFun := fun x => ⟨⟨x, x.property.2⟩, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨x, x.property.1⟩ : A) ⟨t, ht⟩))⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let e := innerCentralizerEquivFixed F t
  refine ⟨e.toMonoidHom.comp f, e.injective.comp ?_⟩
  intro x y h
  exact Subtype.ext (congrArg (fun z => z.val.val) h)


/-- The full fixed group and the actor's embedding use the same literal outer action. -/
theorem outer_actor_orthogonal_embedding {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (A : Subgroup (graphExtension F)) [IsElementaryAbelian 2 A]
    (t : graphExtension F) (ht : t ∈ A) (hout : t ∉ innerPart F) :
    ∃ J : BenderSuzuki.MatrixGroups.HermitianForm 3 F, J.conj = 1 ∧
      Nonempty ((t : MulAut PSL(3,F)).fixedSubgroup ≃* J.specialSubgroup) ∧
      ∃ f : (A ⊓ innerPart F : Subgroup _) →* J.specialSubgroup,
        Function.Injective f := by
  let _ : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  have ht2 : (t : MulAut PSL(3,F)) ^ 2 = 1 :=
    congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian t ht)
  have hnot : ¬ ∃ k, (t : MulAut PSL(3,F)) = MulAut.conj k := by
    rintro ⟨k, hk⟩
    exact hout (show (t : MulAut PSL(3,F)) ∈ MulAut.innerSubgroup PSL(3,F) from ⟨k, hk.symm⟩)
  obtain ⟨J, hJ, ⟨e⟩⟩ := Matrix.PSL3.OddInvolutionFixed.outer_fixed_equiv_orthogonal
    (Group.IsPerfect.not_isSolvable PSL(3,F)) hp ho hF (t : MulAut PSL(3,F)) ht2 hnot
  obtain ⟨f, hf⟩ := actor_inner_fixed_embedding F A t ht
  exact ⟨J, hJ, ⟨e⟩, e.toMonoidHom.comp f, e.injective.comp hf⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
