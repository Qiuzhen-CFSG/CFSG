module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.GroupTheory.AutomorphismSquareOuterTwo

/-!
# Concrete contracts for the terminal component alternatives

The component and residual alternatives below retain actual isomorphisms,
relative C-components, and the original set products. Binary SL₃ and PSL₃
are identified by the checked `Matrix.PSL3Two.equiv`; neither is a family tag.
These definitions specify the remaining source output and do not assert it.

For a perfect residual with one of the three actual quotient models,
the proved outer orders of SL₃(2) and A₆, together with the factor-swap
calculation for a simple square, make its outer group a two-group. This
is the model input to the structural consumer in `Classification.Residuals`.

Source: Aschbacher--Smith 14.6.20--21 and the proof of 14.6.23(1),
printed pp.1037--1038.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification

/-- The two genuine quotient models in original 14.6.20.
The binary SL carrier is identified with PSL₃(2) by `Matrix.PSL3Two.equiv`. -/
@[expose] def ComponentQuotientModels (K : Type*) [Group K] : Prop :=
  Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) ∨
  Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))

open scoped Pointwise

/-- Original 14.6.21 for the fixed original component K.
The second branch uses the actual conjugate by t⁻¹, and normality in the
third branch is relative to H. The products are literal set products. -/
@[expose] def TerminalComponentAlternatives {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (H K : Subgroup G) : Prop :=
  K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
    (((solvableResidual H).map H.subtype = K ∧ ComponentQuotientModels K) ∨
    (Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) ∧
      ∃ t ∈ (T : Subgroup G), t ∉ normalizer (K : Set G) ∧
        ((solvableResidual H).map H.subtype : Set G) =
          (K : Set G) * (K.map (MulAut.conj t⁻¹).toMonoidHom : Set G)) ∨
    (Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) ∧
      ∃ J : Subgroup G, J ≤ H ∧ (J.subgroupOf H).IsCComponent ∧ J ≠ K ∧
        (K.subgroupOf H).Normal ∧ (J.subgroupOf H).Normal ∧
        Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.SL) ∧
        ((solvableResidual H).map H.subtype : Set G) = (K : Set G) * (J : Set G)))

/-- Actual isomorphisms for the image of the terminal solvable residual.
The source component alternatives must construct one of these isomorphisms. -/
@[expose] def ResidualQuotientModels (D : Type*) [Group D] : Prop :=
  Nonempty (D ≃* Matrix.PSL3Two.SL) ∨
  Nonempty (D ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (D ≃* (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL))

theorem ResidualQuotientModels.outer_isTwoGroup
    {D : Type*} [Group D] [Group.IsPerfect D] (h : ResidualQuotientModels D) :
    IsPGroup 2 (MulAut.Outer D) := by
  unfold ResidualQuotientModels at h
  rcases h with hs | ha | hp
  · let e := Classical.choice hs
    exact Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_injective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective
  · let e := Classical.choice ha
    exact (IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card).of_injective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective
  · let e := Classical.choice hp
    let : IsSimpleGroup Matrix.PSL3Two.PSL :=
      Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
    let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
    let f := (MonoidHom.fst Matrix.PSL3Two.SL Matrix.PSL3Two.SL).comp e.toMonoidHom
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨d,hd⟩ := e.surjective (x,1)
      exact ⟨d,congrArg Prod.fst hd⟩
    let : Group.IsPerfect Matrix.PSL3Two.SL := Group.IsPerfect.ofSurjective hf
    let : IsQuasisimple Matrix.PSL3Two.SL := ⟨by
      exact ((QuotientGroup.quotientMulEquivOfEq Matrix.PSL3Two.center_eq_bot).trans
        QuotientGroup.quotientBot).isSimpleGroup⟩
    exact (AutomorphismSquare.outer_isPGroup_two Matrix.PSL3Two.center_eq_bot
      Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup).of_injective
        (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
