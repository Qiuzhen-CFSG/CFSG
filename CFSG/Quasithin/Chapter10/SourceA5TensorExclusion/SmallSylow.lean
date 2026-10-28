module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Intrinsic
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl

/-!
# The small-Sylow obstruction in the A₅ tensor case

The original module lies in L₀ and L₀ normalizes L. Since T does not
normalize L, the module is a proper subgroup of T. Its computed order
therefore rules out the small-Sylow conclusions of the F.1.12 amalgam
alternatives used in source 9.3.1. The nontrivial-core alternative of
Chapter9 remains a separate argument.
Source: Aschbacher–Smith 9.3.1, printed pp.732–733.
-/
public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

include m

theorem fullModule_lt_sylow
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    D.fullModule < (T : Subgroup G) := by
  refine lt_of_le_of_ne m.fullModule_le_sylow ?_
  intro he
  apply hn
  rw [← he]
  exact D.fullModule_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn)

theorem sylow_card_gt_256
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    256 < Nat.card T := by
  by_contra! hc
  have he : D.fullModule = (T : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge m.fullModule_le_sylow (by rw [m.card_fullModule]; exact hc)
  exact (m.fullModule_lt_sylow hn).ne he

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
