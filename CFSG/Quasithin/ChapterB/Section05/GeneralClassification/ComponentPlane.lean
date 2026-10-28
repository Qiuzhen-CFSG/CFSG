module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Complete

/-!
# Components in the small-displacement adequate B.5 alternatives

In the quasisimple alternative, the selected ordinary component is all of
F*(D). The complete source B.5.1 plane sieve then supplies both Irr⁺ and the
four13.7.15 group families. The symmetric-three alternative is solvable and
cannot contain a quasisimple component. The other three adequate structures
retain their original module and group data for the remaining comparison.

Source: Aschbacher–Smith13.7.15(1–2), printed pp.943–944.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- The three adequate alternatives remaining after the component and
plane bounds dispose of the quasisimple and solvable branches. -/
def RemainingComponentCases : Prop :=
  Nonempty (SourceTwoFactorCase ρ) ∨ Nonempty (OuterSixThreeShape D) ∨
    Nonempty (HyperplaneCase ρ)

/-- The full adequate theorem, inspected at an actual component, yields
the source13.7.15 conclusions or one of the three remaining structural cases. -/
theorem component_plane_of_adequate {C A : Subgroup D}
    (hC : IsComponent D C) (hA : IsOffender ρ A)
    (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (h : NontrivialAdequateAlternative ρ) :
    (IsIrrPlus ρ C (moved ρ C) ∧ SmallMoved.ActorList C) ∨ RemainingComponentCases ρ := by
  cases h with
  | quasisimple hq q =>
    have hF : IsComponent D (generalizedFitting D) :=
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩
    have he : C = generalizedFitting D := hC.eq_of_le hF (component_le_generalizedFitting D C hC)
    rw [he]
    let : IsQuasisimple (generalizedFitting D) := hq
    exact Or.inl (SmallMoved.source_irrPlus_and_actor_of_plane ρ hA hd q.sectionData q.clause_one)
  | symmetricThree c =>
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Group.isSolvable_of_isSolvable_injective
        (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    let : Group.IsSolvable D := Group.isSolvable_of_surjective
      (f := c.equiv.symm.toMonoidHom) c.equiv.symm.surjective
    let : IsQuasisimple C := hC.2
    let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
    let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  | twoFactors c => exact Or.inr (Or.inl ⟨c⟩)
  | outerSixThree c => exact Or.inr (Or.inr (Or.inl ⟨c⟩))
  | hyperplane c => exact Or.inr (Or.inr (Or.inr ⟨c⟩))

end CFSG.Quasithin.ChapterB.SourceInduction
