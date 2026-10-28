module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SmallSylow
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Prepared
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SymmetricThree

/-!
# The bounded quasisimple offender actor and its source action

The uniform Sylow bound is applied to the actual composite inclusion
F*(N) ≤ N ≤ D. The component catalogue is bounded without a three-rank
hypothesis. B.5.1(1) then identifies N with that component or supplies its
actual symmetric or full binary G₂ extension. Every group equivalence is
transported from the source action; no group is recognized from its order.

Both the legacy conditional and corrected source-facing adapters are
provided. Neither proof uses the triple-six offender assertion. The full
six-clause module conclusion remains on the original representation for
the remaining Goldschmidt comparison and fixed-space calculations.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1,
pp.99–103, B.5.6(1), p.105, and F.6.18, pp.309–310, in 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
namespace QuasisimpleComparison
universe u v w
variable {A : Type u} [Group A] {B : Type v} [Group B]

/-- Transport the bounded component catalogue through an actual isomorphism. -/
theorem BoundedQuasisimpleModel.comap (e : A ≃* B)
    (h : BoundedQuasisimpleModel B) : BoundedQuasisimpleModel A := by
  cases h with
  | linearTwo F hlo hhi a => exact .linearTwo F hlo hhi (e.trans a)
  | linearThree F hhi a => exact .linearThree F hhi (e.trans a)
  | alternatingSix a => exact .alternatingSix (e.trans a)
  | alternatingSeven a => exact .alternatingSeven (e.trans a)
  | tripleSix a b =>
    have hc : (center A).map e.toMonoidHom = center B := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (Subgroup.centerCongr e ⟨y, hy⟩).property
      · intro hx
        exact ⟨e.symm x, (Subgroup.centerCongr e.symm ⟨x, hx⟩).property,
          e.apply_symm_apply x⟩
    exact .tripleSix ((Subgroup.centerCongr e).trans a)
      ((QuotientGroup.congr _ _ e hc).trans b)
  | g2DerivedTwo a => exact .g2DerivedTwo (e.trans a)
  | linearFourTwo a => exact .linearFourTwo (e.trans a)

/-- The B.5.1 actor after bounding all field parameters. Proper extensions
are retained as the actual symmetric or full binary G₂ group. This is an
intermediate list; its comparison with the F.6.18 rows is still required. -/
def BoundedActorModel (A : Type*) [Group A] : Prop :=
  BoundedQuasisimpleModel A ∨
    (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (A ≃* Equiv.Perm (Fin n))) ∨
      Nonempty (A ≃* Atlas.G2.Model (ZMod 2))

variable {D : Type v} [Group D] [Finite D]
    {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]

private theorem outer_actor (ρ : Representation (ZMod 2) A V)
    (h : OuterNaturalAction ρ) : BoundedActorModel A := by
  rcases h with h | h
  · obtain ⟨n, hlo, hhi, ⟨e⟩⟩ := h
    exact Or.inr (Or.inl ⟨n, hlo, hhi, ⟨e.groupEquiv⟩⟩)
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr ⟨e.groupEquiv⟩)

/-- The actor reduction for the legacy conditional contract. No offender
clause of B.4.2 is used; in particular this does not use the legacy
one-dimensional triple-six assertion to exclude that group. -/
theorem bounded_actor (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (i : A →* D) (hi : Function.Injective i)
    (ρ : Representation (ZMod 2) A V) (hq : IsQuasisimple (generalizedFitting A))
    (c : FFAlternatives.QuasisimpleSourceConclusion ρ (generalizedFitting A)) :
    BoundedQuasisimpleModel (generalizedFitting A) ∧ BoundedActorModel A := by
  have hm := bounded_quasisimple_model small
    (i.comp (generalizedFitting A).subtype) (hi.comp Subtype.val_injective) hq (c.fittingModel ρ)
  refine ⟨hm, ?_⟩
  have whole (h : generalizedFitting A = ⊤) : BoundedActorModel A := by
    let e : A ≃* generalizedFitting A := topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)
    exact Or.inl (hm.comap e)
  cases c.clause_one with
  | irreducible _ _ _ _ he =>
    rcases he with h | ⟨_, h⟩
    · exact whole h
    · exact outer_actor _ h
  | doubleThree _ h _ _ _ => exact whole h
  | naturalDual _ _ h _ => exact whole h
  | repeatedNatural _ _ _ _ _ h _ => exact whole h

/-- The identical group reduction from the corrected full source contract.
All six module clauses remain in the caller's original conclusion. -/
theorem projectiveLine_bounded_actor (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (i : A →* D) (hi : Function.Injective i)
    (ρ : Representation (ZMod 2) A V) (hq : IsQuasisimple (generalizedFitting A))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting A)) :
    BoundedQuasisimpleModel (generalizedFitting A) ∧ BoundedActorModel A := by
  have hm := bounded_quasisimple_model small
    (i.comp (generalizedFitting A).subtype) (hi.comp Subtype.val_injective) hq (c.fittingModel ρ)
  refine ⟨hm, ?_⟩
  have whole (h : generalizedFitting A = ⊤) : BoundedActorModel A := by
    let e : A ≃* generalizedFitting A := topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)
    exact Or.inl (hm.comap e)
  cases c.clause_one with
  | irreducible _ _ _ _ he =>
    rcases he with h | ⟨_, h⟩
    · exact whole h
    · exact outer_actor _ h
  | doubleThree _ h _ _ _ => exact whole h
  | naturalDual _ _ h _ => exact whole h
  | repeatedNatural _ _ _ _ _ h _ => exact whole h
end QuasisimpleComparison

universe u v
/-- Apply the bounded comparison to the actual offender subgroup. This
conditional legacy adapter remains valid without its triple-six offender field. -/
theorem ClassifiedAction.bounded_quasisimple {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ClassifiedAction K ρ G₁ G₂)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : FFAlternatives.QuasisimpleSourceConclusion (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ))) :
    QuasisimpleComparison.BoundedQuasisimpleModel (generalizedFitting (offenderSubgroup ρ)) ∧
      QuasisimpleComparison.BoundedActorModel (offenderSubgroup ρ) :=
  QuasisimpleComparison.bounded_actor h.sylow_card_le
    (offenderSubgroup ρ).subtype Subtype.val_injective _ hq c

/-- Source-facing reduction on the actual offender subgroup, using only
the uniform bound proved from all twelve retained F.6.18 rows. The subgroup
need not be the whole ambient group. -/
theorem ProjectiveLine.ClassifiedAction.bounded_quasisimple {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    QuasisimpleComparison.BoundedQuasisimpleModel (generalizedFitting (offenderSubgroup ρ)) ∧
      QuasisimpleComparison.BoundedActorModel (offenderSubgroup ρ) :=
  QuasisimpleComparison.projectiveLine_bounded_actor h.sylow_card_le
    (offenderSubgroup ρ).subtype Subtype.val_injective _ hq c

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
