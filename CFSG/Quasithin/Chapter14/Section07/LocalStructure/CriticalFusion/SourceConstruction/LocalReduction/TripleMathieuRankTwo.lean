module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuReduction
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TripleCover.Identification
public import Theory.Representation.CentralCubicDegree

/-!
# The guarded rank-two exclusion for a triple-M₂₂ component

The triple-cover reduction supplies the literal star image of the selected
component and its central cubic.  The degree-twelve involution exclusion is a
separate module theorem: it needs the actual star-image cover, normality,
faithful irreducibility and the twelve-dimensional quotient.  This file keeps
those source premises explicit and applies the proved `3.M₂₂` comparison to
every involution in an elementary abelian actor.  No degree or irreducibility
premise is inferred from the central cubic alone.

Source: Aschbacher–Smith 14.7.36 and G.11.2(13), refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Representation.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/- A central cubic and an order-five squaring automizer give the lower bound
   used in the degree-twelve branch.  Keeping the upper bound explicit is the
   source-faithful way to close the equality. -/
omit [Finite G] in
theorem triple_mathieu_degree_twelve_of_upper_bound
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    [Representation.IsIrreducible ρ] [Group.IsPerfect D]
    (hfaith : Function.Injective ρ)
    (hcenter : Nat.card (center D) = 3)
    (x y : D) (hx : orderOf x = 5)
    (hxy : y * x * y⁻¹ = x ^ 2)
    (hupper : Module.finrank (ZMod 2) W ≤ 12) :
    Module.finrank (ZMod 2) W = 12 := by
  apply Nat.le_antisymm hupper
  exact Representation.CentralCubicDegree.finrank_ge_twelve ρ hfaith hcenter x y hx hxy

omit [Finite G] in
/-- Every involution in a literal elementary abelian actor has moved rank
different from two once the selected star-image component is the genuine
triple Mathieu cover in its faithful irreducible degree-twelve action. -/
theorem triple_mathieu_no_rank_two_of_degree_twelve
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (C : Subgroup F.H)
    (e : (C.map (starMap F)) ≃* Sporadic.Mathieu.M22TripleCover)
    (hC : (C.map (starMap F)).Normal)
    (σ : Representation (ZMod 2) (HStar F.H) W)
    [Representation.IsIrreducible
      (σ.comp (C.map (starMap F)).subtype)]
    (hfaith : Function.Injective σ)
    (hdim : Module.finrank (ZMod 2) W = 12)
    (X : Subgroup (HStar F.H)) [IsElementaryAbelian 2 X]
    (g : HStar F.H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace σ g) ≠ 2 := by
  let := hC
  exact Representation.RankTwo.TripleCover.case_thirteen_no_rank_two
    σ (C.map (starMap F)) e hfaith hdim X g hg

/- The same conclusion with the degree discharged by the central-cubic lower
   bound and an explicit source upper bound. -/
omit [Finite G] in
theorem triple_mathieu_no_rank_two_of_upper_bound
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (C : Subgroup F.H)
    (e : (C.map (starMap F)) ≃* Sporadic.Mathieu.M22TripleCover)
    (hC : (C.map (starMap F)).Normal)
    (hperfect : Group.IsPerfect (C.map (starMap F)))
    (σ : Representation (ZMod 2) (HStar F.H) W)
    [Representation.IsIrreducible
      (σ.comp (C.map (starMap F)).subtype)]
    (hfaith : Function.Injective σ)
    (hcenter : Nat.card (center (C.map (starMap F))) = 3)
    (x y : C.map (starMap F)) (hx : orderOf x = 5)
    (hxy : y * x * y⁻¹ = x ^ 2)
    (hupper : Module.finrank (ZMod 2) W ≤ 12)
    (X : Subgroup (HStar F.H)) [IsElementaryAbelian 2 X]
    (g : HStar F.H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace σ g) ≠ 2 := by
  let := hperfect
  have hdim : Module.finrank (ZMod 2) W = 12 :=
    triple_mathieu_degree_twelve_of_upper_bound
      (σ.comp (C.map (starMap F)).subtype)
      (hfaith.comp (C.map (starMap F)).subtype_injective)
      hcenter x y hx hxy hupper
  exact triple_mathieu_no_rank_two_of_degree_twelve C e hC σ hfaith hdim X g hg

/-- The same exclusion applied to the actual central-cubic setup.  The
fixed-free cubic and its scalar relation are retained as part of the returned
record; the rank-two conclusion still consumes the literal degree-twelve
module premises above. -/
theorem original_triple_mathieu_fixedFree_with_no_rank_two
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hCC : C.IsCComponent)
    (ec : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : Representation.BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (hσ : σ.comp (starMap F) = ρ)
    (eσ : (C.map (starMap F)) ≃* Sporadic.Mathieu.M22TripleCover)
    (hσC : (C.map (starMap F)).Normal)
    [Representation.IsIrreducible
      (σ.comp (C.map (starMap F)).subtype)]
    (hfaith : Function.Injective σ)
    (hdim : Module.finrank (ZMod 2) W = 12)
    (X : Subgroup (HStar F.H)) [IsElementaryAbelian 2 X]
    (g : HStar F.H) (hg : g ∈ X) :
    ∃ z : HStar F.H, orderOf z = 3 ∧
      zpowers z = star F (F.Li L 1) ∧
      zpowers z = (center (C.map (starMap F))).map (C.map (starMap F)).subtype ∧
      (∀ v, σ z v = v → v = 0) ∧ σ z ^ 2 + σ z + 1 = 0 ∧
      Module.finrank (ZMod 2) (movedSpace σ g) ≠ 2 := by
  obtain ⟨z,hz,hgen,hcenter,hfree,hpoly⟩ :=
    original_triple_mathieu_fixedFree_scalar d h hab structural previous faithful earlier
      C hCC ec s σ hσ
  exact ⟨z,hz,hgen,hcenter,hfree,hpoly,
    triple_mathieu_no_rank_two_of_degree_twelve C eσ hσC σ hfaith hdim X g hg⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
