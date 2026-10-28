module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLieParabolic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Lie parabolic containing rows in the original Cartan sieve

At the original Sylow, both Hall subgroups, and escaping overgroup, the
whole reduced module supplies the universal Input. The genuine containing
component now excludes nonbinary classical, G₂ and triality quotients,
as well as every large Ree fixed-group quotient. The proper image in
Y/O₂(Y), full seed orbit, and relative normality of the containing orbit
are retained. No escaping cubic or left degree two is assumed.

The unitary and non-Lie cases and the inverted-cubic construction remain
with the local sieve. Source: Aschbacher--Smith 5.1.12--13 and 12.2.2,
printed pp.635--638,795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The literal chosen-module input excludes the classical, G₂, triality
and large Ree containing rows at the original quotient and Cartan pair. -/
theorem rankOne_local_cartan_escape_seed_lie_parabolic_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ ReeF4.IsReeF4Model (C ⧸ pCore 2 C) ∧
        ∀ m : ℕ, 1 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          Chapter1.Section02.LocalModels.IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          ClassicalGroup.IsPSp (C ⧸ pCore 2 C) 2 (2 ^ m) ∨
          ClassificationModels.IsG2At (C ⧸ pCore 2 C) (2 ^ m) ∨
          Triality.Standard.IsTrialityGroupAt (2 ^ m) (C ⧸ pCore 2 C)) :=
  localCartan_escape_seed_lie_parabolic_reduction
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
