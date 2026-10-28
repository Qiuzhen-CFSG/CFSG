module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SelfNormalizer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ComponentwiseInner
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Transport


/-!
# The actual star-quotient Borel action

Let L₀ = ⟨L^T⟩, T₀ = T ∩ L₀, and B = N_{L₀}(T₀). The star projection
identifies B* with the intrinsic normalizer of T₀* in L₀*. Under the source
noncontainment assumption and solvability of B, its order is prime to three,
Y₀* preserves both B* and T₀*, and [B*,Y₀*] lies in T₀*. These are the
quotient facts used by the torus/field-automorphism calculation.

The proofs use the actual normalizer projection and its surjectivity, so
no factor orbit or two-core kernel is dropped. This module does not assert
B = T₀ or that the field exponent is one.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
`refs/quasithin.pdf`, printed p.1144, proof of 15.3.49(k).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual intersection T ∩ ⟨L^T⟩ in the ambient group. -/
def sylowIntersection (L : Subgroup G) (T : Sylow 2 G) : Subgroup G :=
  (T : Subgroup G) ⊓ localSpan L T

/-- The relative normalizer N_{⟨L^T⟩}(T ∩ ⟨L^T⟩). -/
def relativeBorel (L : Subgroup G) (T : Sylow 2 G) : Subgroup G :=
  localSpan L T ⊓ normalizer (sylowIntersection L T : Set G)

variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

omit [Finite G] in
/-- The Borel image is the full intrinsic normalizer, not just a subgroup of it. -/
lemma star_borel_eq_normalizer :
    (starImage H (relativeBorel L T)).subgroupOf (starImage H (localSpan L T)) =
      normalizer ((starImage H (sylowIntersection L T)).subgroupOf
        (starImage H (localSpan L T)) : Set (starImage H (localSpan L T))) := by
  rw [← ModelSelection.starProjection_map H (localSpan L T) (relativeBorel L T)
    (ModelSelection.closure_le d) inf_le_left]
  exact ModelSelection.starProjection_normalizer_map H (localSpan L T)
    (sylowIntersection L T) (ModelSelection.closure_le d) inf_le_right
    (ModelSelection.closure_projection_ker_le_inter d)

/-- Noncontainment makes the actual Sylow image Y₀*-invariant. -/
lemma star_sylow_normalized (hout : ¬ Y0 ≤ localSpan L T) :
    starImage H Y0 ≤ normalizer (starImage H (sylowIntersection L T) :
      Set (H ⧸ pCore 2 H)) := by
  have hn := (replacement_sylow_intersection H M Y0 L T d.replacement d.sylow_le
    d.theta_eq d.sylow_normalizes d.commutator_eq d.cubic_quotient hout).2
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [← starImage_commutator H (sylowIntersection L T) Y0
    (inf_le_right.trans (ModelSelection.closure_le d))
    ((d.theta_eq ▸ theta_le _).trans inf_le_right)]
  exact map_mono (comap_mono (le_normalizer_iff_commutator_le_left.mp
    (le_sup_left.trans hn)))

/-- The actual Borel image is Y₀*-invariant. -/
lemma star_borel_normalized [Group.IsSolvable (relativeBorel L T)]
    (hout : ¬ Y0 ≤ localSpan L T) :
    starImage H Y0 ≤ normalizer (starImage H (relativeBorel L T) :
      Set (H ⧸ pCore 2 H)) := by
  have hn := (d.borel_control (relativeBorel L T) hout rfl).2.1
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [← starImage_commutator H (relativeBorel L T) Y0
    (inf_le_left.trans (ModelSelection.closure_le d))
    ((d.theta_eq ▸ theta_le _).trans inf_le_right)]
  exact map_mono (comap_mono (le_normalizer_iff_commutator_le_left.mp
    (le_sup_left.trans hn)))

/-- The action on the Borel is trivial modulo the Sylow image. -/
lemma star_borel_commutator_le [Group.IsSolvable (relativeBorel L T)]
    (hout : ¬ Y0 ≤ localSpan L T) :
    ⁅starImage H (relativeBorel L T), starImage H Y0⁆ ≤
      starImage H (sylowIntersection L T) := by
  rw [← starImage_commutator H (relativeBorel L T) Y0
    (inf_le_left.trans (ModelSelection.closure_le d))
    ((d.theta_eq ▸ theta_le _).trans inf_le_right)]
  exact map_mono (comap_mono (d.borel_control (relativeBorel L T) hout rfl).2.2.2.2.2)

/-- The intrinsic star normalizer inherits its order prime to three from B. -/
lemma star_normalizer_three_free [Group.IsSolvable (relativeBorel L T)]
    (hout : ¬ Y0 ≤ localSpan L T) :
    ¬ 3 ∣ Nat.card (normalizer ((starImage H (sylowIntersection L T)).subgroupOf
      (starImage H (localSpan L T)) : Set (starImage H (localSpan L T)))) := by
  have hthree := (d.borel_control (relativeBorel L T) hout rfl).2.2.2.1
  let f := ModelSelection.normalizerProjection H (localSpan L T)
    (sylowIntersection L T) (ModelSelection.closure_le d) inf_le_right
    (ModelSelection.closure_projection_ker_le_inter d)
  have hf := ModelSelection.normalizerProjection_surjective H (localSpan L T)
    (sylowIntersection L T) (ModelSelection.closure_le d) inf_le_right
    (ModelSelection.closure_projection_ker_le_inter d)
  exact fun h => hthree (h.trans (card_dvd_of_surjective f hf))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse
