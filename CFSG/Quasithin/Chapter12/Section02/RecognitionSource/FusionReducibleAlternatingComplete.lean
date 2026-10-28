module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternatingSix
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternatingEightGeometry

/-!
# The alternating-row producer for 12.2.16

The literal row-(d) action on V/C_V(L) reconstructs the augmentation core
in degree six or eight; nonzero fixed space excludes the odd degrees.
The six-letter core has global TI by its two odd orbits and the containment
N_G(T) ≤ N_G(L). In degree eight the original L/O₂(L) actor is recovered,
and outside fusion constructs the weight-two/complement pair with the
literal C_T(v) Sylow witness. Thus every alternating geometry premise of
the reducible-row consumer is discharged.

The second theorem applies that producer to the original module alternatives
and adjusts the seed to AlternatingEightFusion. Its G₂ input and the proof
of the Sylow-normalizer containment remain with the reducible-row assembly;
the terminal A₈ omega-center argument is a subsequent source step.

Source: Aschbacher–Smith, 12.2.2(3d), printed p.795, and 12.2.16,
printed pp.799–800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The complete alternating-row producer, conditional only on the independent
Sylow-normalizer containment in addition to the original source inputs. -/
theorem alternating_of_sylow_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural n)) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V) := by
  exact alternating_of_core_geometry D h.quasisimple hne
    (globalTI_of_alternating_six_core h D structural hnone hNT)
    (alternatingEight_core_geometry h D structural hnone hne) n hlo hhi e

/-- Application to the original reducible-row consumer, discharging its entire
alternating input and constructing the adjusted fusion configuration. -/
theorem reducible_of_g2_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (g2 : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype) →
        IsTISubgroup V) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V) := by
  exact reducible_of_geometric_rows h D structural hnone rows hne
    (alternating_of_sylow_normalizer h D structural hnone hne hNT) g2

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
