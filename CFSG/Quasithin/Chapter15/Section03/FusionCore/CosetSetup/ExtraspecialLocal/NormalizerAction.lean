module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction.WreathModel
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.PrimeSupport
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.LocalControl

/-!
# The fixed-plane normalizer and 15.3.49(4) ⇒ (5)

The compatible natural-action coordinates identify `S = N_T(V₁)` with the
part of the Sylow image whose coordinate shift is trivial. Thus `Z_S = C_V(S)`
corresponds to its fixed space. The concrete wreath calculation gives exactly
`N_{Mbar}(Z_S) = Tbar`, through the given actor map.

The genuine 15.3.46(5) input then gives `N_G(Z_S) = M ∩ N_G(Z_S)`. Its image
is a two-group, so its two-residual centralizes `V`. The prime restriction
on `C_M(V)` from 15.3.49(4) therefore makes `N_G(Z_S)` prime to three.
Only these earlier inputs are assumed; neither the normalizer image nor its
prime restriction is a hypothesis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122 and 1141–1143, especially the first paragraph of p.1143.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction

open Subgroup WreathModel
attribute [local instance] orthogonalAction

variable {G : Type*} [Group G] {M V : Subgroup G}

private theorem normalizer_iff_coordinatePredicate
    (d : NaturalOrthogonalAction M V) (H : Subgroup G) (hHV : H ≤ V)
    (F : OrthogonalVector → Prop)
    (hF : ∀ v : V, (v : G) ∈ H ↔ F (d.coordinates v)) (m : M) :
    (m : G) ∈ normalizer (H : Set G) ↔
      ∀ w, F w ↔ F (d.actor m • w) := by
  constructor
  · intro hn w
    obtain ⟨v, rfl⟩ := d.coordinates.surjective w
    rw [← d.compatible]
    exact (hF v).symm.trans ((Subgroup.mem_normalizer_iff.mp hn v).trans
      (hF (V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v)))
  · intro hn
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    have hV : x ∈ V ↔ (m : G) * x * (m : G)⁻¹ ∈ V :=
      Subgroup.mem_normalizer_iff.mp (d.normalizes m.property) x
    constructor
    · intro hx
      have ht := (hn (d.coordinates ⟨x, hHV hx⟩)).mp ((hF _).mp hx)
      rw [← d.compatible] at ht
      exact (hF _).mpr ht
    · intro hx
      let v : V := ⟨x, hV.mpr (hHV hx)⟩
      apply (hF v).mpr
      apply (hn (d.coordinates v)).mpr
      rw [← d.compatible]
      exact (hF _).mp hx

private theorem mem_plane_coordinates (d : NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) (v : V) :
    (v : G) ∈ d.plane i ↔ ∀ j, j ≠ i → d.coordinates v j = 1 := by
  constructor
  · rintro ⟨u, hu, he⟩
    have he' : u = v := Subtype.ext he
    subst u
    exact hu
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem normalizes_plane_iff (d : NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) (m : M) :
    (m : G) ∈ normalizer (d.plane i : Set G) ↔ (d.actor m).right = 1 := by
  exact (normalizer_iff_coordinatePredicate d (d.plane i) (d.plane_le i)
    (fun v => ∀ j, j ≠ i → v j = 1) (mem_plane_coordinates d i) m).trans
    (plane_iff_shift (d.actor m) i)

private theorem compatible_fix_iff (d : NaturalOrthogonalAction M V) (m : M) (v : V) :
    d.actor m • d.coordinates v = d.coordinates v ↔
      (m : G) * (v : G) = (v : G) * (m : G) := by
  rw [← d.compatible]
  constructor
  · intro h
    have he := congrArg Subtype.val (d.coordinates.injective h)
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro h
    apply congrArg d.coordinates
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr h)

private theorem mem_fixedPlane_coordinates (d : NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (i : OrthogonalPlaneIndex) (v : V) :
    (v : G) ∈ fixedPlane V (planeStabilizer T (d.plane i)) ↔
      baseFixed (d.image (T : Subgroup G)) (d.coordinates v) := by
  constructor
  · intro hv a ha hr
    obtain ⟨m, hm, rfl⟩ := ha
    apply (compatible_fix_iff d m v).mpr
    exact hv.2 m ⟨hm, (normalizes_plane_iff d i m).mpr hr⟩
  · intro hv
    refine ⟨v.property, ?_⟩
    intro s hs
    let m : M := ⟨s, hTM hs.1⟩
    apply (compatible_fix_iff d m v).mp
    exact hv (d.actor m) ⟨m, hs.1, rfl⟩ ((normalizes_plane_iff d i m).mp hs.2)

/-- Membership in the actual local normalizer is detected by the Sylow actor image. -/
theorem normalizes_fixedPlane_iff [Finite G] (d : NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (i : OrthogonalPlaneIndex) (m : M) :
    (m : G) ∈ normalizer (fixedPlane V (planeStabilizer T (d.plane i)) : Set G) ↔
      d.actor m ∈ d.image (T : Subgroup G) := by
  let P := (T.subtype hTM).mapSurjective d.onto
  exact (normalizer_iff_coordinatePredicate d _ inf_le_left _
    (mem_fixedPlane_coordinates d T hTM i) m).trans (sylow_normalizer P (d.actor m))

/-- The source calculation `N_{Mbar}(Z_S) = Tbar` for the supplied compatible action. -/
theorem image_normalizer_fixedPlane [Finite G] (d : NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex) :
    d.image (M ⊓ normalizer (fixedPlane V (planeStabilizer T (d.plane i)) : Set G)) =
      d.image (T : Subgroup G) := by
  apply le_antisymm
  · rintro a ⟨m, hm, rfl⟩
    exact (normalizes_fixedPlane_iff d T hTM i m).mp hm.2
  · rintro a ⟨m, hm, rfl⟩
    exact ⟨m, ⟨m.property, (normalizes_fixedPlane_iff d T hTM i m).mpr
      ⟨m, hm, rfl⟩⟩, rfl⟩

/-- Source 15.3.49(4) implies (5), using the normalizer containment of 15.3.46(5).
The unused prime restriction on `M ∩ H` is not needed for this implication. -/
theorem lemma_15_3_49_5_of_centralizer_three_prime [Finite G]
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (d : NaturalOrthogonalAction M (localModule T M)) (i : OrthogonalPlaneIndex)
    (hN : normalizer (fixedPlane (localModule T M)
      (planeStabilizer T (d.plane i)) : Set G) ≤ M)
    (hc : Nat.Coprime 3 (Nat.card (M ⊓ centralizer (localModule T M : Set G) : Subgroup G))) :
    normalizer (fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) : Set G) =
      M ⊓ normalizer (fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) : Set G) ∧
    Nat.Coprime 3 (Nat.card
      (normalizer (fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) : Set G))) := by
  let N := normalizer (fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) : Set G)
  have he : N = M ⊓ N := (inf_eq_right.mpr hN).symm
  refine ⟨he, ?_⟩
  have hi : d.image N = d.image (T : Subgroup G) :=
    (congrArg d.image he).trans (image_normalizer_fixedPlane d T hTM i)
  have hp : IsPGroup 2 (d.image N) := by
    rw [hi]
    exact (T.isPGroup'.comap_subtype (K := M)).map d.actor
  exact three_prime_of_residual_bound N M (localModule T M) hN hc
    ((d.residual_le_centralizer_of_image_isTwoGroup hN hp).trans inf_le_right)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction
end
