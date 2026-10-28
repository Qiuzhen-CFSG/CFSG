module
public import Theory.Representation.BinaryPermutation.EightCoreNormalizer
public import Theory.Representation.BinaryPermutation.EightCoreOrbits
/-!
# Orbit preservation in the binary eight-point modules

An additive automorphism normalizing the A₈ action preserves every orbit
on the augmentation core and its natural quotient. Orbit sizes distinguish
all core weights except complementary pairs; preservation of weight two
and the inverse automorphism separate weights two and six. The natural
quotient has two nonzero orbits of different sizes.

This supplies the literal nonsingular Sylow selection in Aschbacher--Smith,
Section 12.6, printed pp.823--824, without interchanging the two core lifts.
-/

public section
namespace BinaryPermutation
open EightCore

theorem eight_core_weight_of_orbit_image
    (e : core (Fin 8) ≃+ core (Fin 8))
    (he : ∀ x : core (Fin 8),
      e '' (Set.range fun a : alternatingGroup (Fin 8) =>
        alternatingCoreRepresentation (Fin 8) a x) =
      Set.range fun a : alternatingGroup (Fin 8) =>
        alternatingCoreRepresentation (Fin 8) a (e x))
    (v : core (Fin 8)) : wordWeight (e v).val = wordWeight v.val := by
  have hc := congrArg Set.ncard (he v)
  rw [Set.ncard_image_of_injective _ e.injective, orbit_card, orbit_card] at hc
  have hs : ∀ x, e.symm '' (Set.range fun a : alternatingGroup (Fin 8) =>
      alternatingCoreRepresentation (Fin 8) a x) =
      Set.range fun a : alternatingGroup (Fin 8) =>
        alternatingCoreRepresentation (Fin 8) a (e.symm x) := by
    intro x
    have h := congrArg (Set.image e.symm) (he (e.symm x))
    simpa only [Set.image_image, e.symm_apply_apply, e.apply_symm_apply, Set.image_id'] using h.symm
  have hsep := (equal_size_iff v (e v)).mp hc
  rcases weights v with hv | hv | hv | hv | hv
  · rw [(weight_zero_iff v).mp hv, map_zero]
  · rw [hv]
    exact eight_core_weight_two_of_orbit_image e he v hv
  · omega
  · have hnot : wordWeight (e v).val ≠ 2 := by
      intro h
      have hh := eight_core_weight_two_of_orbit_image e.symm hs (e v) h
      rw [e.symm_apply_apply, hv] at hh
      contradiction
    omega
  · have hnot : wordWeight (e v).val ≠ 0 := by
      intro h
      have hv0 : v = 0 := e.injective ((weight_zero_iff (e v)).mp h |>.trans e.map_zero.symm)
      rw [hv0] at hv
      have hz : wordWeight (0 : core (Fin 8)).val = 0 := (weight_zero_iff _).mpr rfl
      omega
    omega

theorem eight_core_orbit_preserved
    (e : core (Fin 8) ≃+ core (Fin 8))
    (he : ∀ x : core (Fin 8),
      e '' (Set.range fun a : alternatingGroup (Fin 8) =>
        alternatingCoreRepresentation (Fin 8) a x) =
      Set.range fun a : alternatingGroup (Fin 8) =>
        alternatingCoreRepresentation (Fin 8) a (e x))
    (v : core (Fin 8)) :
    ∃ a : alternatingGroup (Fin 8), alternatingCoreRepresentation (Fin 8) a v = e v := by
  rw [← Set.mem_range, even_core_orbit_eq_weight (by decide)]
  exact eight_core_weight_of_orbit_image e he v

theorem eight_natural_orbit_preserved
    (e : natural (Fin 8) ≃+ natural (Fin 8))
    (he : ∀ x : natural (Fin 8),
      e '' (Set.range fun a : alternatingGroup (Fin 8) =>
        alternatingNaturalRepresentation (Fin 8) a x) =
      Set.range fun a : alternatingGroup (Fin 8) =>
        alternatingNaturalRepresentation (Fin 8) a (e x))
    (v : natural (Fin 8)) :
    ∃ a : alternatingGroup (Fin 8), alternatingNaturalRepresentation (Fin 8) a v = e v := by
  by_cases hv : v = 0
  · subst v
    exact ⟨1, by simp⟩
  have hc := congrArg Set.ncard (he v)
  rw [Set.ncard_image_of_injective _ e.injective] at hc
  exact eight_natural_orbitCardSeparates v (e v) hv (by simpa using hv) hc
end BinaryPermutation
