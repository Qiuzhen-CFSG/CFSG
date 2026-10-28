module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Inputs
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements

/-!
# The two outstanding inputs to the source normal-closure calculation

The seed input identifies the literal centralizer residual with the residual
of an actual maximal parabolic of L₀T, and proves its Xi and wreath-action
properties. The independent invariant-component input performs the further
sieve using that actual wreath quotient. Neither proposition is asserted
here. In particular, the general adequate embedding theorem alone does not
prove the short list or the full automorphism-group quotient.

Source: Aschbacher--Smith 10.2.4, printed p.747, applied to the centralizer
seed of 10.2.11 and §10.3, pp.753,756--757. The seed input deliberately
does not assume the later S₅-wreath recognition, so it can also be used in
the non-Bender branch of 10.3.3.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- The actual S₃ wreath C₂ carrier in source 10.2.4. -/
abbrev ParabolicWreath :=
  RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))

/-- Recognition data to be constructed from the original natural module.
All Xi properties concern the residual of the stated parabolic; the
residual equality connects them to the literal centralizer seed. -/
structure ParabolicSeedData (L : Subgroup G) (z : G) where
  parabolic : Subgroup G
  sylow_le : (T : Subgroup G) ≤ parabolic
  le_join : parabolic ≤ localJoin T L
  maximal : IsCoatom (parabolic.subgroupOf (localJoin T L))
  residual : (pResidual 2 parabolic).map parabolic.subtype = centralizerSeed T L z
  xi : (pResidual 2 parabolic).map parabolic.subtype ∈ Xi G (T : Subgroup G)
  quotient : XiOddQuotient 3 (XiQuotient
    ((pResidual 2 parabolic).map parabolic.subtype))
  wreath : Nonempty ((parabolic ⧸ pCore 2 parabolic) ≃* ParabolicWreath)

/-- The earlier natural-module and maximal-parabolic recognition obligation.
No normal-closure or later component-model conclusion is assumed. -/
def ParabolicSeedAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s),
    Nonempty (ParabolicSeedData T L (d.first * d.second))

/-- The additional invariant sieve in 10.2.4. The input is the actual
S₃-wreath quotient of XT, with full local and relative-normality data.
Held is not an input row: the adequate Held alternative is retained by
the assembly independently. -/
def InvariantWreathSieveAt : Prop :=
  ∀ X P H I : Subgroup G,
    LocalInput 3 (T : Subgroup G) X P H →
    IsSQTK KnownSimple.IsKnownSimple H →
    I ∈ cComponentsIn H → IsQuasisimple (XiQuotient I) →
    (I.subgroupOf H).Normal → (T : Subgroup G) ≤ normalizer (I : Set G) →
    P ≤ I → X ≤ I → ⁅I,P⁆ = I →
    Nonempty (((X ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G)) ≃* ParabolicWreath) →
    Alternatives 3 (T : Subgroup G) P I →
    ∃ k : ℕ, (k = 4 ∨ k = 5) ∧ ClassicalGroup.IsPSL (XiQuotient I) k 2 ∧
      Nonempty (((I ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G)) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin k) (ZMod 2)))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
