module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.Action
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructure.OriginalFlag
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.ModelImage

/-!
# The source normalizer escape in 14.7.70

The genuine projection of M = N_G(L) onto L/O₂(L), marked by the original
flag, and the proved finite parabolic residual-image theorem discharge both
local premises of the projection–residual argument. Under Y ≤ M, the
projected Y is the marked line residual A₄ and T ∩ L acts nontrivially on E.
The actual full E-action then gives Y = [Y,T ∩ L] ≤ L. Consequently the
original span E = ⟨V₁^Y⟩ lies in V, contradicting Z_alpha ≰ V.

The escape theorem assumes only the original source data, preceding geometry,
core facts, and the complete universal Structural1222 implication. The last
input belongs to qt-12-02-reduction; its applicability to the original
d.natural.source and d.natural.chosen is proved by the projection constructor.
There is no local projection, model-image, commutator or escape premise.

The Thompson consumer uses the original uniqueness over LT, the full
EarlierSetupResults contracts (Chapter 1/12 setup owners), and literal
14.3.9(2), EarlierThompsonNormality (qt-14-03-prelim). Discharge of those
earlier universal inputs and construction of the preceding geometry and core
facts stay with the source-theorem assembly owners. The remaining small
subnormal witness and full 14.7.70 assembly belong to
qt-14-07-rechoice-comparison-thompson-witness and its Goldschmidt parent.

This extension imports the independent constructors after the conditional
reduction, preserving its API and avoiding an import cycle.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed p.1074 (PDF p.1091).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
open Chapter12.Section08 Stellmacher
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) {c : CriticalPath (L := L) F}

/-- The literal source escape from N_G(L), with both local construction
premises discharged and the genuine earlier universal setup kept explicit. -/
theorem normalizer_escape
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (h : Geometry d c) (k : CoreFacts c) :
    ¬ Y c ≤ normalizer (L : Set G) :=
  NormalizerStructure.normalizer_escape_of_source d structural parabolicImageTheorem h k

/-- Apply the established normalizer escape to the original Thompson
argument, preserving uniqueness over LT and the actual two-core of I. -/
theorem thompson_escape
    (h : Geometry d c) (k : CoreFacts c)
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (thompson : EarlierThompsonNormality.{u}) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2 :=
  thompson_not_le_core_of_escape d c earlier thompson
    (normalizer_escape d earlier.structural h k)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
