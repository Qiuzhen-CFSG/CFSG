module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Contracts

/-!
# Remaining source inputs for the centralizer geometry

The fixed-space/TI argument, the local two-core argument, and the escaping
centralizer argument have independent conditional proofs. All three concern
the same original fundamental setup and survivor. The latter two may use
the conclusions of the first as explicit hypotheses, so their construction
does not wait for that proof. These propositions are outstanding proof
obligations; they assert no source theorem by themselves.

Source: Aschbacher--Smith 10.2.10--11 and 10.3.1--2, printed pp.753--756.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- Source 10.3.1, with the TI conclusion established using 10.2.10. -/
def FixedSpaceTIAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (_s : SourceLinearThreeSurvivor T D),
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
    ∀ g : G,
      ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆

/-- The required parts of source 10.2.11(2--3), on literal fixed vectors
and literal X, K_z and V_z. The source hypotheses preceding that lemma are
explicit here, rather than replaced by an already constructed CentralizerData. -/
def CoreReducedAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D),
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ →
    (∀ g : G,
      ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆) →
    ∀ a b : G, a ∈ ⁅D.fullModule,L⁆ →
      b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom →
      a ≠ 1 → b ≠ 1 →
      a ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) →
      b ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) →
      a * b ∈ centerIn (T : Subgroup G) → orderOf (a * b) = 2 →
      D.fullModule ≤ (centralizer ({a * b} : Set G)).pCoreIn 2 ∧
      (centralizerSeed T L (a * b) < componentSpan T L (a * b) →
        IsPReduced 2 ((centralizerModule a b).subgroupOf
          (centralizer ({a * b} : Set G))))

/-- Original 10.3.2, for each actual central involution in V. This argument
does not require the two-core containment or reducedness in CoreReducedAt. -/
def EscapeAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (_s : SourceLinearThreeSurvivor T D),
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ →
    (∀ g : G,
      ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆) →
    ∀ z ∈ D.fullModule, z ∈ centerIn (T : Subgroup G) → orderOf z = 2 →
      ¬ centralizer ({z} : Set G) ≤ D.maximalLocal

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry
