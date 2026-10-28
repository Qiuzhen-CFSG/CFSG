module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.OvergroupTransport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.MathieuOvergroup

/-!
# Conditional J₄ stabilizer reduction through an embedded Mathieu overgroup

An invariant overgroup H with quotient M₂₄ transfers the stabilizer calculation
to the actual image of A. The isomorphism of two-core sections comes from the
restricted projection, including its possibly nontrivial image core. The
resulting inner conjugator then lifts to A by `OvergroupTransport`.

The M₂₄ stabilizer calculation and the existence of an invariant Mathieu
overgroup for every source-local L₄(2) section remain separate premises.
Consequently this file does not yet prove the unconditional J₄ assertion in
the proof of 1.3.9. In particular A.3.12(17)'s quotient label is not used as
an embedded-overgroup theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.12(14),(17),
printed pp.47–48; proof of 1.3.9, printed p.514.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer

universe u
variable {G : Type u} [Group G]

/-- The smaller quotient identification is transported through the actual
projection and the specified overgroup isomorphism. -/
theorem image_isPSL [Finite G] {A : Subgroup G} {α : MulAut G}
    (D : InvariantMathieuOvergroup A α)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2) :
    ClassicalGroup.IsPSL
      (XiQuotient ((twoQuotientImage A D.overgroup).map D.quotientEquiv.toMonoidHom)) 4 2 := by
  let e := D.quotientEquiv.subgroupMap (twoQuotientImage A D.overgroup)
  let eQ := QuotientGroup.congr (pCore 2 (twoQuotientImage A D.overgroup))
    (pCore 2 ((twoQuotientImage A D.overgroup).map D.quotientEquiv.toMonoidHom))
    e (pCore_map_iso 2 e)
  exact hA.of_mulEquiv ((imageSectionEquiv D.le_overgroup).trans eQ).symm

/-- Conditional lifting from a supplied invariant Mathieu overgroup. -/
theorem isInnerOnTwoQuotient_of_mathieuOvergroup [Finite G]
    (hmathieu : MathieuFourStabilizerTheorem) {A : Subgroup G}
    (hmodel : ClassicalGroup.IsPSL (XiQuotient A) 4 2) (α : MulAut G)
    (htwo : ∃ n : ℕ, α ^ (2 ^ n) = 1) (hA : A.map α.toMonoidHom = A)
    (D : InvariantMathieuOvergroup A α) : IsInnerOnTwoQuotient A α := by
  apply isInnerOnTwoQuotient_of_invariant_overgroup D.le_overgroup α htwo hA D.invariant
  apply TwoStabilizerActsInner.of_map D.quotientEquiv
  exact hmathieu _ D.sylow (image_isPSL D hmodel) D.image_extension D.image_local

/-- Conditional assembly with the exact source hypotheses. Both model
premises must be discharged before this gives the J₄ source theorem. -/
theorem twoStabilizerActsInner_of_mathieuOvergroups
    (hgeometry : JankoFourInvariantMathieuTheorem.{u})
    (hmathieu : MathieuFourStabilizerTheorem)
    {Q : Type u} [Group Q] [Finite Q] (e : Q ≃* Janko4.Model)
    (A : Subgroup Q) (S : Sylow 2 Q)
    (hmodel : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents (S : Subgroup Q)) :
    TwoStabilizerActsInner A := by
  intro α htwo hA
  obtain ⟨D⟩ := hgeometry Q e A S hmodel hlocal α htwo hA
  exact isInnerOnTwoQuotient_of_mathieuOvergroup hmathieu hmodel α htwo hA D

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
