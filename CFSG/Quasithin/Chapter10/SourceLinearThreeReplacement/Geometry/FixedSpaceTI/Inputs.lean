module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.FixedReduction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.GlobalLower

/-!
# The remaining numerical inputs to the original fixed-space contradiction

The two bounds concern different actual modules and can be proved independently.
The first is the involution displacement/global-centralizer bound on V; the
second supplies an actual H*-invariant submodule of the omega-center orbit U,
moved by W₀, with the source fixed-space-family bound.
Neither includes fixed-space vanishing, TI, or the desired contradiction.
Their consumer uses the proved weak-closure movement and E.3.6 argument.

Source: Aschbacher--Smith 10.3.1, pp.755--756, using I.1.6, B.4.8,
10.2.3(3), 10.2.8, and the direct sum/tensor A₅-module calculation.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The source proves s(G,V)=2 in the nonzero-fixed branch; this is the
precise weaker inequality consumed by E.3.6. -/
def GlobalSAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D),
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥ →
    letI : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
    1 < globalS D.fullModule

/-- The source H* constituent step, with its original inclusion and action.
The witness is an elementary H-invariant subgroup of U=⟨Ω₁Z(T)^H⟩ moved by W₀,
whose actual H-image has parameter at most one. No bound on the whole U is
required. Abstract model constituents without this connection do not suffice. -/
def HStarLocalAAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (_s : SourceLinearThreeSurvivor T D),
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥ →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
    ∃ I : Subgroup G, I ≤ omegaModule T H ∧
      H ≤ normalizer (I : Set G) ∧
      ¬ indexedWeakClosure D.fullModule (T : Subgroup G) 0 ≤ centralizer (I : Set G) ∧
      ∃ hI : IsElementaryAbelian 2 I, letI := hI
        moduleA ((automizerRepresentation I).comp (inducedAutomizer I H).subtype) ≤ 1

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
