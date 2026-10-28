module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroNormalizerControl
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOrthogonalAction

/-!
# An escaping A₅ Baumann normalizer supplies the original orthogonal action

The completed zero-center normalizer argument forces a nontrivial fixed
center whenever the Baumann normalizer escapes the original maximal local
subgroup. The positive-center recognition then supplies the full orthogonal
action on the original commutator module, retaining both plane markings.

Source: Aschbacher–Smith, 10.2.1, printed p.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_fixed_center_ne_bot_of_escape
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥ := by
  intro hz
  exact hout (source_a5_zero_baumann_normalizer_le D e hn hz)

/-- The orthogonal action requires no remaining fixed-center premise. -/
theorem source_exists_escaping_orthogonal_action
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourceFixedCenterOrthogonalAction D :=
  source_exists_fixed_center_orthogonal_action D e hn
    (source_a5_fixed_center_ne_bot_of_escape D e hn hout) hout

end CFSG.Quasithin.Chapter10
