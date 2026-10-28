module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.DoubleNaturalSplitting
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.BinaryOffender.QuadraticDualOffender

/-!
# Source B.4.9 splitting in the strict L₄ module argument

The binary four-dimensional specialization of B.4.9 applies to the actual
natural submodule and its natural-or-dual quotient. We transport the fixed
GL₄(2) actor marking to the standard SL₄(2) matrix action and construct the
quotient intertwiner using that same marking. Faithful quadratic action
makes the given order-four actor elementary abelian; its displacement kernel
is exactly the fixed space required by B.4.9.

The resulting invariant complement discharges `TwoFactorSplitting` for every
actor. The second theorem applies it to the head-axis and socle-center
exclusions used in the strict branch of 13.8.25. Chief-factor recognition and
the source geometry remain separate prerequisites of that branch.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.9(1),
printed pp.92–94, and 13.8.25, printed p.961/PDF p.978.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterB.NaturalExtensions
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
open ChiefFactors SplittingCyclic.AxisExclusions
universe u v

variable {H : Type u} [Group H]

/-- The precise binary four-dimensional B.4.9 input, with both quotient
orientations and the original invariant submodule. -/
theorem twoFactorSplitting_source : TwoFactorSplitting.{u, v} H := by
  intro V _ _ _ σ eH K hσ hK hQ E hE hquad haxis
  obtain ⟨eK, heK⟩ := hK
  let natural : ActionEquiv K.toRepresentation (linearNatural BinaryField.two 4) := {
    groupEquiv := eH.trans (BinaryLinear.OuterCyclic.slEquivLinear 4).symm
    linearEquiv := eK
    intertwines := by
      intro g v
      change eK (K.toRepresentation g v) =
        BinaryLinear.OuterCyclic.slEquivLinear 4
          ((BinaryLinear.OuterCyclic.slEquivLinear 4).symm (eH g)) (eK v)
      rw [heK]
      rw [MulEquiv.apply_symm_apply] }
  have hquot : Nonempty (Representation.Equiv K.quotientRepresentation K.toRepresentation) ∨
      Nonempty (Representation.Equiv K.quotientRepresentation K.toRepresentation.dual) := by
    rcases hQ with ⟨eQ, heQ⟩ | ⟨eQ, heQ⟩
    · left
      refine ⟨Representation.Equiv.mk (eQ.trans eK.symm) ?_⟩
      intro g
      apply LinearMap.ext
      intro v
      apply eK.injective
      change eK (eK.symm (eQ (K.quotientRepresentation g v))) =
        eK (K.toRepresentation g (eK.symm (eQ v)))
      rw [eK.apply_symm_apply, heQ, heK, eK.apply_symm_apply]
    · right
      refine ⟨Representation.Equiv.mk (eQ.trans eK.dualMap) ?_⟩
      intro g
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro v
      change (eQ (K.quotientRepresentation g f)) (eK v) =
        eQ f (eK (K.toRepresentation g⁻¹ v))
      rw [heQ, heK]
      rfl
  let d : DoubleNatural BinaryField.two 4 σ := {
    faithful := hσ
    space := K
    natural := natural
    quotient := hquot }
  have hs : QuadraticSplitting.SourceHypotheses d := by
    refine ⟨Or.inr ⟨rfl, le_rfl⟩, ⟨E, ?_, hquad, by omega⟩, by simp [BinaryField.two]⟩
    obtain ⟨P, hP, hfixed⟩ := haxis
    refine ⟨elementary_of_faithful_quadratic σ hσ E hquad, hE, P, hP, ?_⟩
    intro g hg hne
    rw [← hfixed g hg hne]
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    change K.quotientRepresentation g v = v ↔ K.quotientRepresentation g v - v = 0
    exact sub_eq_zero.symm
  obtain ⟨C, hC⟩ := CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.doubleNatural_splits d hs
  refine ⟨C, ?_, ?_⟩
  · apply Subrepresentation.toSubmodule_injective
    exact hC.disjoint.eq_bot
  · apply Subrepresentation.toSubmodule_injective
    exact hC.codisjoint.eq_top

/-- The two nonsplitting exclusions in 13.8.25 now follow from the proved
B.4.9 theorem, without an additional two-factor splitting hypothesis. -/
theorem nonsplitting_exclusions_source
    {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (W : Subrepresentation ρ) (hW : IsCoatom W) (hW0 : W ≠ ⊥)
    (hunique : ∀ X : Subrepresentation ρ, IsCoatom X → X = W)
    (hhead : IsNatural W.quotientRepresentation eH)
    (Vγ : Subgroup H) [IsElementaryAbelian 2 Vγ] (hq : IsQuadratic ρ Vγ) :
    (∀ A : Subgroup H, A ≤ Vγ → ¬ IsCyclic A →
      ¬ FixesHyperplane W.quotientRepresentation A) ∧
    (∀ I : Subrepresentation ρ, IsAtom I → I ≤ W →
      ∀ A : Subgroup H, A ≤ Vγ → ¬ IsCyclic A →
        ¬ HasCommonCenter I.toRepresentation A) :=
  nonsplitting_exclusions ρ eH twoFactorSplitting_source hchief W hW hW0 hunique hhead Vγ hq

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
