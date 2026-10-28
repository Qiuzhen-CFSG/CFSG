module

public import Theory.GroupTheory.SylowOvergroupCharacteristic
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups

/-!
# Generalized Fitting subgroups of proper Sylow overgroups in GL₅(2)

The checked flag exhaustion supplies a nonempty proper cut for a proper
Sylow overgroup. Its subspace radical is normal in the corresponding full
parabolic and self-centralizing. Sylow maximality puts that radical inside
the overgroup, so its intrinsic generalized Fitting subgroup is its two-core.

The actual PSL₅(2) comparison is exported by the imported model module.
The field and dimension restrictions of the flag theorem are preserved.
Source: Aschbacher–Smith B.1.13, printed p.74; GLS III, 2.6.5(e).
-/

public section

open Subgroup Theory.GroupTheory
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic

/-- Proper Sylow-two overgroups in the actual binary five-dimensional group
have characteristic two, without assuming solvability. -/
theorem generalizedFitting_eq_twoCore_of_sylow_le
    (S : Sylow 2 (LinearGroup 5)) (X : Subgroup (LinearGroup 5))
    (hSX : (S : Subgroup (LinearGroup 5)) ≤ X) (hX : X ≠ ⊤) :
    generalizedFitting X = pCore 2 X := by
  let : Finite (LinearGroup 5) :=
    Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5))
      DFunLike.coe_injective
  obtain ⟨b, cuts, hcuts⟩ := isFlagParabolic_of_sylow_le S X hSX
  have hn : cuts.Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    exact hX (by simpa only [he, flagStabilizer_empty] using hcuts)
  obtain ⟨i, hi⟩ := hn
  have hXP : X ≤ parabolic (flagSpace b i) := by
    rw [hcuts]
    exact (flagStabilizer_antitone b (Set.singleton_subset_iff.mpr hi)).trans
      (flagStabilizer_singleton b i).le
  exact generalizedFitting_eq_pCore_of_sylow_le_normalizer S X
    (parabolic (flagSpace b i)) (radical (flagSpace b i)) hSX hXP
    (radical_le_parabolic _) (parabolic_le_normalizer _) (radical_two _)
    (centralizer_radical_le (flagSpace_ne_bot b i) (flagSpace_ne_top b i))

end BinaryLinear.FiveFlagGeometry
