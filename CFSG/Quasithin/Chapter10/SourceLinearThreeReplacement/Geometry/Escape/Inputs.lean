module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Inputs
public import CFSG.Quasithin.ChapterI.Section06To08.Basic

/-!
# The two source steps in the diagonal-centralizer contradiction

The first step uses diagonal fusion and point-centralizer control to make
the original full module TI, under the temporary assumption that the chosen
central involution has its centralizer in M. The second is a calculation on
the actual pair of natural linear-three factors: a faithful elementary
rank-four subgroup cannot have the same fixed subgroup for every nonidentity
element. Both are proof obligations, not asserted source theorems.

The consumer in `Escape.Assembly` constructs the offending subgroup from
w=2 and the TI-pair theorem. It retains responsibility for discharging these
two inputs before asserting `Geometry.EscapeAt` unconditionally.

Source: Aschbacher--Smith, 10.3.2, printed p.756, PDF p.773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
open Chapter3.Section02 ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The first paragraph of 10.3.2, retaining the original moved-factor TI
hypothesis and the temporary centralizer-containment assumption. -/
def WholeModuleTIAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (_s : SourceLinearThreeSurvivor T D),
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ →
    (∀ g : G,
      ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆) →
    ∀ z ∈ D.fullModule, z ∈ centerIn (T : Subgroup G) → orderOf z = 2 →
      centralizer ({z} : Set G) ≤ D.maximalLocal → IsTISubgroup D.fullModule

/-- The concrete pair-action obstruction in the last sentence of 10.3.2.
The actor and all centralizers are literal subgroups of the original G. -/
def PairFixedSpaceAt : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (_s : SourceLinearThreeSurvivor T D),
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ →
    ∀ A : Subgroup G, A ≤ D.maximalLocal → IsElementaryAbelian 2 A →
      Representation.BinaryOffender.rank A = 4 →
      A ⊓ centralizer (D.fullModule : Set G) = ⊥ →
      ∃ a ∈ A, a ≠ 1 ∧
        D.fullModule ⊓ centralizer ({a} : Set G) ≠
          D.fullModule ⊓ centralizer (A : Set G)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
