module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Uniqueness

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Rank
public import Theory.GroupTheory.SolvableNormalizerObstruction
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.FiniteLocalPair
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.SpecificGroups.PSL3Two.NonSolvable
public import CFSG.Quasithin.Chapter3.Defs

/-!
# Comparing the two escaping central choices in original 13.4.12: structure at the original group

The four-group V ∩ Ω₁Z(T) contains the fixed generator. Its other two points
have different weights. If both escape, the source parabolic alternatives
force O²(H₄,₂) to be normalized by N_G(J(T)). Maximal two-locality puts that
residual inside the normalizer; the actual L₃(2) quotient then kills its
solvable image. This contradicts its non-two-group property, which follows
from its Sylow supplement and H₄,₂ lying outside M.

The residual's nontrivial two-core is proved using characteristic-two
inheritance, so it is not an extra geometric assumption. The comparison
retains both literal two-residuals, the common Sylow, fixed-line centralizers,
and the SL₃(2) model of the quotient. The model simplicity theorem reuses
the attributed ATLAS port in Order168Models; see LICENSES/ATLAS.txt.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/Uniqueness` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory CFSG.Quasithin
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {D : ChosenModule T L V}
namespace CoreMarking

/-- The source central four-group reduces uniqueness to exclusion of the
simultaneous weight-two and weight-four escapes. -/
theorem unique_escape_of_weight_exclusion_at (m : CoreMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hcard : Nat.card (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) ≤ 4)
    (hpair : ∀ v w : V,
      v.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      m.weight v = 2 → m.weight w = 4 →
      ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → False)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (w : V) (hw1 : w ≠ 1)
    (hwT : w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hwout : ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G)) : w = z := by
  have nonfixed (v : V) (hv1 : v ≠ 1)
      (hvout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G)) :
      v.val ∉ centralizer (L : Set G) := by
    intro hv
    exact hvout (fixed_generator_centralizer_at h structural D m ⟨v.property, hv⟩
      (fun he => hv1 (Subtype.ext he))).le
  have hz := nonfixed z hz1 hzout
  have hw := nonfixed w hw1 hwout
  have hd : m.constant.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omega_iff (D := D) m.constant).mpr
    apply mem_centralizer_iff.mpr
    intro t ht
    exact (mem_centralizer_iff.mp
      (normalizer_component_le_fixed_centralizer_at h structural D m
        (D.sylow_normalizes_component ht)) m.constant.val
      ⟨m.constant.property, m.constant_fixed⟩).symm
  apply m.central_weight_injective _ inf_le_left hcard ⟨m.constant.property, hd⟩
    z w ⟨z.property, hzT⟩ ⟨w.property, hwT⟩ hz
  rcases m.nonfixed_weight z hz with hz | hz <;>
    rcases m.nonfixed_weight w hw with hw | hw
  · omega
  · exact (hpair z w hzT hwT hz hw hzout hwout).elim
  · exact (hpair w z hwT hzT hw hz hwout hzout).elim
  · omega
end CoreMarking
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
universe u
variable {G : Type u} [Group G] [Finite G]

open Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
