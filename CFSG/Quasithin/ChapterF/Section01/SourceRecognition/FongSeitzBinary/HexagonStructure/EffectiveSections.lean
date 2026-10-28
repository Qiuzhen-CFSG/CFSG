module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.LocalActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.EffectiveSections

/-!
# Effective radical actions on the original and geometric markings

Apply the linear (5D)--(5F) argument to the literal original Sylow image
and its reflected intersection. The effective binary representation uses
these same representatives, with an explicit right-conjugation equation.
The original SourceQuotient application preserves the quotient map Q.q.
The general amalgam marking also covers the universal/geometric carrier.

The marking-level statement includes every binary field size. A second
application uses the proved original linear local identification and kernel
containments; only that identification's acting-factor perfectness premise
is required. This does not restrict the final classification to perfect
factors. Generic nonperfect identification remains with source recognition.

Source: Fong--Seitz I (5D)--(5F), printed pp.26--28, as used by (6E),
pp.43--45. The complete earlier structural inputs for GTwoSource and
TrialitySource, including nonlinear exclusions and irreducibility, remain
obligations of the hexagon family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

/-- The actual original/geometric radical has faithful effective action.
    This marking-level statement includes every binary field size. -/
theorem marked_linear_effective_radical
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* PSL(2,F)) :
    ∃ d : RootSection Q split j,
      d.numerator = (MarkedLocal.sylowMap Q e h).range ⊓
        rightConjugate (MarkedLocal.sylowMap Q e h).range
          ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D) ∧
      d.denominator = ⊥ ∧ d.IsEffective ∧ Function.Injective d.effectiveRepresentation := by
  let s := UnitarySource.actorReflection Q split j
  let d := radicalSection Q split j hKj
  refine ⟨d, marked_radical_eq h Q e split j s.val s.class_eq, rfl, ?_, ?_⟩
  · exact linear_radical_effective Q split j hKj μ s hm i hij hKi
  · exact d.effectiveRepresentation_injective
      (linear_radical_effectiveAction_injective Q split j hKj μ s hm i hij hKi)

/-- The newly recognized original linear factor discharges the local model
    premise; original linear regularity discharges both kernel inclusions.
    Only the acting original factor is required to be perfect. -/
theorem effective_radical_of_original_linear_factors
    {F E : Type*} [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2]
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F)) :
    ∃ d : RootSection Q split j,
      d.numerator = (MarkedLocal.sylowMap Q e h).range ⊓
        rightConjugate (MarkedLocal.sylowMap Q e h).range
          ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D) ∧
      d.denominator = ⊥ ∧ d.IsEffective ∧ Function.Injective d.effectiveRepresentation := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact marked_linear_effective_radical Q e h split hm i j hij
    (MarkedLocal.linear_remainder_le_kernel Q e h split i Ti hTi μi)
    (MarkedLocal.linear_remainder_le_kernel Q e h split j Tj hTj μj)
    (MarkedLocal.linearLocalEquiv Q e h split j hpj Tj hTj μj)

/-- The effective representation uses the same original S representatives
    and the source's right-conjugation convention. -/
theorem marked_effective_action (j : Fin 2) (d : RootSection Q split j)
    (r : MarkedLocal.originalRankOne Q e split j) (x y : S)
    (hx : MarkedLocal.sylowMap Q e h x ∈ d.numerator)
    (hy : MarkedLocal.sylowMap Q e h y ∈ d.numerator)
    (hxy : MarkedLocal.sylowMap Q e h y =
      (MarkedLocal.originalRankOneEquiv Q e split j r : X ⧸ Q.D)⁻¹ *
        MarkedLocal.sylowMap Q e h x * (MarkedLocal.originalRankOneEquiv Q e split j r : X ⧸ Q.D)) :
    d.effectiveRepresentation (MarkedLocal.originalRankOneEquiv Q e split j r)⁻¹
      (Additive.ofMul (QuotientGroup.mk (⟨MarkedLocal.sylowMap Q e h x,hx⟩ : d.numerator))) =
        Additive.ofMul (QuotientGroup.mk (⟨MarkedLocal.sylowMap Q e h y,hy⟩ : d.numerator)) := by
  rw [d.effectiveRepresentation_mk]
  congr 2
  apply Subtype.ext
  simpa only [d.numeratorAction_apply, coe_inv, inv_inv] using hxy.symm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The source quotient application retains the literal original quotient map Q.q. -/
theorem quotient_effective_radical_of_original_linear_factors
    {F E : Type*} [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F)) :
    ∃ d : RootSection Q split j,
      d.numerator = ((S.subgroupOf (generated L S)).map Q.q) ⊓
        rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
          ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D) ∧
      d.denominator = ⊥ ∧ d.IsEffective ∧ Function.Injective d.effectiveRepresentation := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := effective_radical_of_original_linear_factors Q (originalMarkedIso Q) h split
    hm i j hij hpj μi μj
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
