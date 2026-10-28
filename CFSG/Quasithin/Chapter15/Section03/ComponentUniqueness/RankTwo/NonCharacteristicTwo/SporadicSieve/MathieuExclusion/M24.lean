module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.M24.Reduction
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.OctadSeeds
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalSeeds
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups

/-!
# The M₂₄ exclusion from the full rank-two local configuration

Every normalizer in the 22-row Sylow catalogue lies in an actual octad,
trio or sextet local subgroup. Source maximality at characteristic two
forces equality with this geometric overgroup. The image of Y₊ is normal
and solvable there, and its full S₃ × S₃ Frattini shadow forces a factor
of nine in its order, contradicting the native normal-seed bounds.

The final theorem discharges both intrinsic geometry premises using the
proved catalogue and native stabilizer actions. Automorphism innerness
identifies the whole component quotient, so no extension premise remains.
Source: Aschbacher--Smith, 15.3.41--42, printed p.1138, and 1.1.5(3f),
printed p.502; GLS3, Table 5.3e.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion

/-- Assembly with explicit native normalizer coverage and elementary
normal-seed bounds. The octad branch is discharged here. -/
theorem not_m24_of_local_geometry
    {G : Type*} [Group G] [Finite G] {I L M Y S : Subgroup G}
    [(L.subgroupOf I).Normal] (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* M24)
    (ho : EvenCatalogue.NormalizerOvergroups)
    (hs : ∀ (k : Fin 2) (D : Subgroup (EvenCandidates.localGroup k)),
      D.Normal → Group.IsSolvable D → ¬ 9 ∣ Nat.card D) : False :=
  M24Reduction.not_m24_of_overgroups_and_seed_bounds ho
    ⟨EvenCatalogue.octad_normal_solvable_not_nine, hs⟩ d e

/-- The actual M₂₄ carrier cannot occur in the full source component setup.
The native geometry discharges every additional premise of the reduction. -/
theorem not_m24
    {G : Type*} [Group G] [Finite G] {I L M Y S : Subgroup G}
    [(L.subgroupOf I).Normal] (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* M24) : False :=
  not_m24_of_local_geometry d e EvenCatalogue.normalizerOvergroups
    EvenCatalogue.elementary_normalizer_seed_bounds

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion
