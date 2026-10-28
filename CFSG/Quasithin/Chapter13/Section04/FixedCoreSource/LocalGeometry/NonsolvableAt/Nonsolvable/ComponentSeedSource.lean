module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSeedAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentSeedSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CentralSeedParabolics
public import Theory.GroupTheory.ReducedNormal.ComponentSeedSplitting

/-!
# The source component orbit and its splitting: structure at the original group

For K contained in the original involution centralizer and normalized by T,
the involution gives KT a nontrivial two-core. Ambient characteristic two
then applies to KT. The Sylow-fixed seed theorem proves
V_H = [V_H,K] C_Z(K) for the literal V_H = ⟨Z^K⟩ and Z = Ω₁Z(T).

The component marking now gives the full order-four seed and the outside
parabolic's relative centralizer identities without a splitting premise.
ComponentSelection constructs K from the earlier source inputs; excluding
the A₅, covered-A₆ and doubled-natural rows remains with
qt-d-1341-nonsolvable-source. The earlier structural/index inputs retain
final discharge with qt-d-1341-fixed-core-source. This is not completion of
13.4.10 or the nonsolvable branch.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/ComponentSeedSource` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V K : Subgroup G} {D : ChosenModule T L V}

/-- The three source module rows yield the full central seed, with no
independent splitting or full-seed containment premise. -/
theorem full_seed_of_component_moved_module_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (DK : ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆)
    (marking : ComponentModuleAt DK z.val) :
    omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  exact full_seed_of_component_split_at h structural m z hz1 hzT hindex DK marking hKz hKM
    (component_seed_split h₀ hzT (fun he => hz1 (Subtype.ext he)) hKz
      DK.sylow_normalizes_component)
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
