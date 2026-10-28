module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FirstPair

/-!
# Self-normalizing Sylow subgroups in binary linear covers

The invariant cuts of a full binary flag determine its normalizer, so a
Sylow two-subgroup is self-normalizing in every positive binary dimension.
The same equality lifts through a two-group kernel, which lies in the
original Sylow subgroup. This retains the original quotient map.

Source application: Aschbacher--Smith 10.2.9, printed p.752, for the
binary-four and binary-five containing components.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.SylowNormalizerCover
open OuterCyclic InvariantNodeActions

private instance (n : ℕ) : Finite (LinearGroup n) := Finite.of_injective
  (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

theorem normalizer_sylow_eq {m : ℕ} (S : Sylow 2 (LinearGroup (m+1))) :
    normalizer (S : Set (LinearGroup (m+1))) = S := by
  change normalizer ((S : Subgroup (LinearGroup (m+1))) : Set (LinearGroup (m+1))) = (S : Subgroup (LinearGroup (m+1)))
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  rw [hb]
  exact SylowFlagOvergroups.normalizer_fullFlag_eq b

theorem normalizer_sylow_eq_of_two_kernel {H : Type*} [Group H] [Finite H]
    {m : ℕ} (f : H →* LinearGroup (m+1)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 H) :
    normalizer (S : Set H) = S := by
  have hker : f.ker ≤ (S : Subgroup H) := hk.le_sylow_of_normal S
  apply le_antisymm _ (S : Subgroup H).le_normalizer
  intro x hx
  have hm := (S : Subgroup H).le_normalizer_map f (mem_map_of_mem f hx)
  have he := normalizer_sylow_eq (S.mapSurjective hf)
  change normalizer ((S : Subgroup H).map f : Set (LinearGroup (m+1))) =
    (S : Subgroup H).map f at he
  rw [he] at hm
  have hx' : x ∈ ((S : Subgroup H).map f).comap f := hm
  rwa [comap_map_eq,sup_of_le_left hker] at hx'
end BinaryLinear.SylowNormalizerCover

