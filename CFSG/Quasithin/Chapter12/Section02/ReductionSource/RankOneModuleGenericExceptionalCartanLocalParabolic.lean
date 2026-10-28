module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalParabolic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The classical containing rows in the original Cartan sieve

The original whole reduced module supplies the universal rank-one Input.
At the same Sylow, Cartan pair and escaping overgroup, the source seed and
its actual containing C-component have no PSL₃(2ᵐ), SL₃(2ᵐ) or PSp₄(2ᵐ) two-core
quotient for m > 1. Both Hall conditions, the full seed orbit, its strict
containment and relative normality of the containing orbit are retained.

This discharges these three containing-model rows in 5.1.13.
The remaining Lie and sporadic rows, together
with construction of the inverted cubic, remain with the original sieve.
Source: Aschbacher--Smith 5.1.12--13 and 12.2.2,
printed pp.635--636,795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 input excludes the projective/special linear-three and
symplectic-four containing rows without a cubic or invariant-seed premise. -/
theorem rankOne_local_cartan_escape_seed_parabolic_reduction
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
        ∀ m : ℕ, 1 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          Chapter1.Section02.LocalModels.IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          ClassicalGroup.IsPSp (C ⧸ pCore 2 C) 2 (2 ^ m)) :=
  localCartan_escape_seed_parabolic_reduction
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
