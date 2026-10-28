module
public import CFSG.Quasithin.Chapter10.SourceNormalizationSurvivor
public import Theory.SpecificGroups.SymmetricFive.WreathTwoCore
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Literal centralizer data for the linear-three replacement

Here X is O²(C_{L₀}(z)), not O₂(C_{L₀}(z)). Its G_z-conjugate span
is K_z, and the E-conjugate span is V_z. These definitions retain the
original inclusions in G. The three propositions below are independent
source obligations, with their earlier inputs explicit; none is an instance
or a theorem asserting that the obligation has been discharged.

Source: Aschbacher--Smith 10.2.11 and 10.3.1--3, printed pp.753--757.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

def centralizerSeed (L : Subgroup G) (z : G) : Subgroup G :=
  (pResidual 2 (localOrbit T L ⊓ centralizer ({z} : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer ({z} : Set G)).subtype

def componentSpan (L : Subgroup G) (z : G) : Subgroup G :=
  conjugateSpanBy (centralizerSeed T L z) (centralizer ({z} : Set G))

def componentJoin (L : Subgroup G) (z : G) : Subgroup G :=
  componentSpan T L z ⊔ (T : Subgroup G)

def centralizerModule (v₁ v₂ : G) : Subgroup G :=
  conjugateSpanBy (zpowers v₁ ⊔ zpowers v₂)
    (centralizer ({v₁ * v₂} : Set G))

/-- The actual diagonal central involution and the conclusions of the
central-fixed-part, TI, escape and reduced-module arguments. Reducedness
is conditional on X<K_z, exactly as in 10.2.11(2). -/
structure CentralizerData {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) where
  first : G
  second : G
  first_mem : first ∈ ⁅D.fullModule,L⁆
  second_mem : second ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom
  first_ne : first ≠ 1
  second_ne : second ≠ 1
  first_fixed : first ∈ centralizer
    (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G)
  second_fixed : second ∈ centralizer
    (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G)
  fixed_part : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥
  moved_ti : ∀ g : G,
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆
  central : first * second ∈ centerIn (T : Subgroup G)
  order : orderOf (first * second) = 2
  escape : ¬ centralizer ({first * second} : Set G) ≤ D.maximalLocal
  full_core : D.fullModule ≤ (centralizer ({first * second} : Set G)).pCoreIn 2
  module_centralizer : centralizer ({first * second} : Set G) ⊓
    centralizer (centralizerModule first second : Set G) ≤ D.maximalLocal
  reduced : centralizerSeed T L (first * second) < componentSpan T L (first * second) →
    IsPReduced 2 ((centralizerModule first second).subgroupOf
      (centralizer ({first * second} : Set G)))

/-- Source 10.3.1--2 and the required literal 10.2.11 conclusions. -/
def CentralizerGeometryAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D), Nonempty (CentralizerData T D s)

/-- Source 10.3.3, including the component orbit identified by 10.2.4.
This is an actual wreath isomorphism, not a group-family label. -/
def WreathRecognitionAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s),
    Nonempty ((componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃*
      Theory.SpecificGroups.SymmetricFive.WreathComponents.W) ∧
    centralizerSeed T L (d.first * d.second) < componentSpan T L (d.first * d.second) ∧
    ¬ componentSpan T L (d.first * d.second) ≤ D.maximalLocal ∧
    ∀ K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)),
      componentOrbit K (T : Subgroup G) = componentSpan T L (d.first * d.second)

/-- The final overgroup calculation J_z=K_z. Its conclusion concerns the
original X and literal conjugate spans, not maximality of a replacement. -/
def OvergroupSpanAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s),
    Nonempty ((componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃*
      Theory.SpecificGroups.SymmetricFive.WreathComponents.W) →
    centralizerSeed T L (d.first * d.second) < componentSpan T L (d.first * d.second) →
    ¬ componentSpan T L (d.first * d.second) ≤ D.maximalLocal →
    (∀ K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)),
      componentOrbit K (T : Subgroup G) = componentSpan T L (d.first * d.second)) →
    ∀ M : Subgroup G, IsMaximalTwoLocal M → componentJoin T L (d.first * d.second) ≤ M →
      conjugateSpanBy (centralizerSeed T L (d.first * d.second)) M =
        componentSpan T L (d.first * d.second)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
