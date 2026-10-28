module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Unramified.LocalRing

namespace Theory.AlgebraicGroup.Bor1

open IsLocalRing

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A local, essentially finite-type, formally unramified flat algebra over a
regular local ring is regular local. -/
public theorem isRegularLocalRing_of_formallyUnramified_of_flat
    [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    [Module.Flat R S] :
    IsRegularLocalRing S := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hover : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨by
      simpa [Ideal.under_def] using
        (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  rw [← hmap]
  refine le_trans (b := (↑(maximalIdeal R).spanFinrank : WithBot ℕ∞)) ?_ ?_
  · exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap R S)
      (maximalIdeal R).fg_of_isNoetherianRing
  · rw [(isRegularLocalRing_iff R).mp inferInstance,
      ← maximalIdeal_height_eq_ringKrullDim,
      ← maximalIdeal_height_eq_ringKrullDim,
      Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
        (maximalIdeal R) (maximalIdeal S)]
    exact_mod_cast le_add_right
      (show (maximalIdeal R).height ≤ (maximalIdeal R).height from le_rfl)

end Theory.AlgebraicGroup.Bor1
