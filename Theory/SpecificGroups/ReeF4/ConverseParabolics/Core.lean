module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics
public import Theory.PGroupCore

/-!
# From root radicals to intrinsic Ree parabolic cores

A root-defined radical normalized by its full parabolic is contained in the
parabolic's intrinsic two-core: its two-group property is already proved from
the positive root matrices. Centralizer antitonicity then transfers a
self-centralization calculation for this radical to the two-core. Neither the
order of the radical nor an identification of the full Levi quotient is needed.

Source: the local characteristic-two condition in Aschbacher–Smith, §0.1,
printed pp.3–4 (`refs/quasithin.pdf`). Normalization and self-centralization
of the specified radical remain explicit root-calculation inputs here.
-/

public section
namespace ReeF4.ConverseParabolics
open Subgroup LargeLocalSeeds

/-- Normality is relative to the full parabolic. -/
theorem intrinsicRadical_le_pCore {m : ℕ} {s : Side}
    (hnorm : parabolic m s ≤ normalizer (radical m s : Set (Model m))) :
    intrinsicRadical m s ≤ pCore 2 (parabolic m s) := by
  have hn : (intrinsicRadical m s).Normal :=
    (normal_subgroupOf_iff_le_normalizer (radical_le_parabolic m s)).mpr hnorm
  exact le_sSup ⟨hn, intrinsicRadical_isPGroup m s⟩

/-- Self-centralization of the concrete root radical implies the required
condition for the intrinsic two-core. -/
theorem centralizer_pCore_le_of_radical {m : ℕ} {s : Side}
    (hnorm : parabolic m s ≤ normalizer (radical m s : Set (Model m)))
    (hc : centralizer (intrinsicRadical m s : Set (parabolic m s)) ≤
      intrinsicRadical m s) :
    centralizer (pCore 2 (parabolic m s) : Set (parabolic m s)) ≤
      pCore 2 (parabolic m s) :=
  (centralizer_le (intrinsicRadical_le_pCore hnorm)).trans
    (hc.trans (intrinsicRadical_le_pCore hnorm))

end ReeF4.ConverseParabolics
