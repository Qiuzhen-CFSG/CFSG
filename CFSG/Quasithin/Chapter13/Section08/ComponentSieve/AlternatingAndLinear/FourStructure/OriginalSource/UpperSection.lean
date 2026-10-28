module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.DualLowerBound.UpperSection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.ModuleAction
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Chosen
public import CFSG.Quasithin.Chapter13.Section07.SpanGrowth

/-!
# The literal upper section in the strict critical-pair case

The quotient map from V_H to V_H/U_H has the original kernel and conjugation
formula. Linearizing its H/O₂(H)-action constructs the `UpperSection` used by
the critical-pair comparison. No alternative quotient or actor is chosen.

The original 13.7.3(6) commutator conclusion supplies action descent. The
preceding F.9 hypothesis, H≤G₁ and noncentral local commutator remain explicit
source inputs. Elementary abelianness follows from the standing abelian span.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.7.3(6),
13.8.4(6), and 13.8.11, printed pp.936,947–950.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource
open CriticalTransfer.PairConsequences
open SolvableExclusion.Three.Supercritical.Offenders
open TransvectionRecognition.Component.ModelExtension SourceCompletion
variable {G : Type*} [Group G]

/-- Retain the literal quotient map when linearizing its conjugation action. -/
noncomputable def upperSectionOfStarAction
    {H V U : Subgroup G} [(U.subgroupOf V).Normal]
    [IsElementaryAbelian 2 V] (a : SolvableExclusion.Five.StarAction H V U)
    (hVH : V ≤ H) (hUV : U ≤ V) : UpperSection H V U (linearAction a) where
  le := hVH
  normalizes := a.normalizes
  kernel_le := hUV
  quotient := {
    toFun := fun v => Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' (U.subgroupOf V) v))
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  surjective := QuotientGroup.mk'_surjective _
  kernel := QuotientGroup.ker_mk' _
  conjugates := fun h v => congrArg Additive.ofMul (a.conjugation h v)

variable [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The standing abelian span supplies the elementary upper numerator. -/
theorem vh_elementary_source (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHG : H ≤ G₁) : IsElementaryAbelian 2 (Source.VH H V) := by
  let := d.span_elementary
  exact IsElementaryAbelian.of_le (conjugateSpanBy_mono (le_refl V) hHG)

/-- Construct the actual upper-section action from the original local setup
and the earlier commutator theorem. -/
theorem exists_upperSection_source
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hHG : H ≤ G₁) (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    [IsElementaryAbelian 2 (Source.VH H V)] :
    ∃ (τ : Representation (ZMod 2) (Source.Hstar H)
        (Additive (Source.Vsection H V V₃))),
      Nonempty (UpperSection H (Source.VH H V) (Source.UH H V₃) τ) := by
  have hcore : ⁅Source.VH H V, Source.QH H⁆ ≤ Source.UH H V₃ :=
    (Section07.source_commutator_conclusions (localNaturalSetup d) hF9 hHG hcomm).2.2.2.2.le
  obtain ⟨a⟩ := SolvableExclusion.Five.exists_starAction H (Source.VH H V)
    (Source.UH H V₃) (le_normalizer_conjugateSpanBy V H)
    (le_normalizer_conjugateSpanBy V₃ H) hcore
  exact ⟨linearAction a, ⟨upperSectionOfStarAction a
    (conjugateSpanBy_le_self hF9.V_le_H) (conjugateSpanBy_mono d.seed_le le_rfl)⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource
