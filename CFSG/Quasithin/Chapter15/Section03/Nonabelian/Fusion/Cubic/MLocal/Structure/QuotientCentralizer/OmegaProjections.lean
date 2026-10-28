module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientAction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientCentralizer.OmegaProjections.Model

/-!
# Nontrivial cubic projections to the two Omega factors

If a nonidentity cubic centralizes a definite plane and lies in just one
S₃ factor, the model calculation supplies a nonzero invariant functional.
Compatibility with the actual conjugation action puts all commutators
with that factor in the functional's proper kernel. This contradicts
[V,Nᵢ] = V. Interchanging the two factor coordinates gives both nontrivial
projections. The Omega factors are specified by their actual image
isomorphism and full displacement, independently of the definite planes.

The proof transports conjugation and commutators through the given vector
coordinates; it needs neither an ambient normality assumption nor a
centralizer equality. The natural quotient pair wrapper supplies exactly
the two projection premises consumed by the quotient centralizer reduction.
The construction and placement of the selected source cubic remain with
that reduction's assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.53(1),
15.3.54(4), 15.3.58(2), and the setup of 15.3.60, printed pp.1146–1150.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
open OrthogonalGeometry OmegaProjections
private instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction
variable {G : Type*} [Group G] {M V : Subgroup G}

private theorem not_full_displacement (d : NaturalOrthogonalAction M V)
    {N : Subgroup G} (hNM : N ≤ M)
    (χ : OrthogonalVector →* Multiplicative (ZMod 2))
    (hne : ∃ w, χ w ≠ 1)
    (hinv : ∀ n : N, ∀ w, χ (d.actor ⟨n, hNM n.property⟩ • w) = χ w) :
    ⁅V, N⁆ ≠ V := by
  have hcomm : ⁅N, V⁆ ≤ χ.ker.map d.vectorEmbedding := by
    apply commutator_le.mpr
    intro n hn v hv
    let m : M := ⟨n, hNM hn⟩
    let w := d.coordinates ⟨v, hv⟩
    have he : d.vectorEmbedding w = v := by
      simp [w, NaturalOrthogonalAction.vectorEmbedding]
    refine ⟨d.actor m • w * w⁻¹, ?_, ?_⟩
    · change χ (d.actor m • w * w⁻¹) = 1
      rw [map_mul, map_inv, hinv ⟨n, hn⟩, mul_inv_cancel]
    · rw [map_mul, map_inv, d.vectorEmbedding_conjugate, he]
      rfl
  intro hmove
  have hV : V ≤ χ.ker.map d.vectorEmbedding :=
    (hmove.symm.trans (commutator_comm V N)).le.trans hcomm
  obtain ⟨w, hw⟩ := hne
  have hm : d.vectorEmbedding w ∈ χ.ker.map d.vectorEmbedding :=
    hV (d.coordinates.symm w).property
  exact hw ((mem_map_iff_mem d.vectorEmbedding_injective).mp hm)

private theorem second_projection_ne_one (d : NaturalOrthogonalAction M V)
    (I : Subgroup G) (hIM : I ≤ M)
    (e : d.image I ≃* OrthogonalPlaneActor × OrthogonalPlaneActor)
    (hmoves : ⁅V, firstOmegaFactor d I hIM e⁆ = V)
    (i : OrthogonalPlaneIndex) (a : I) (hpow : a ^ 3 = 1)
    (hne : d.actor ⟨a, hIM a.property⟩ ≠ 1)
    (hcentral : (a : G) ∈ centralizer (d.plane i : Set G)) :
    (e (imageActor d I hIM a)).2 ≠ 1 := by
  intro hsecond
  let x := (e (imageActor d I hIM a)).1
  let f : OrthogonalPlaneActor →* OrthogonalActor :=
    (d.image I).subtype.comp
      (e.symm.toMonoidHom.comp (MonoidHom.inl OrthogonalPlaneActor OrthogonalPlaneActor))
  have he : (imageActor d I hIM a : OrthogonalActor) = f x := by
    change _ = (e.symm (x, 1) : OrthogonalActor)
    congr 1
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext rfl hsecond
  have hx : x ^ 3 = 1 := by
    have hp : e (imageActor d I hIM a) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, hpow, map_one, map_one]
    exact congrArg Prod.fst hp
  have hfx : f x ≠ 1 := by rw [← he]; exact hne
  have hpoint : d.actor ⟨a, hIM a.property⟩ ∈ pointwise (orthogonalCoordinatePlane i) := by
    have h : (⟨a, hIM a.property⟩ : M) ∈
        (centralizer (d.plane i : Set G)).subgroupOf M := hcentral
    rwa [d.plane_eq_map, d.centralizer_map_eq_comap] at h
  have hfix : ∀ w : OrthogonalVector, (∀ j, j ≠ i → w j = 1) → f x • w = w := by
    rw [← he]
    exact hpoint
  obtain ⟨χ, hχ, hinv⟩ := invariant_functional_of_plane_cubic f x hx hfx i hfix
  have hNM : firstOmegaFactor d I hIM e ≤ M := (map_subtype_le _).trans hIM
  apply not_full_displacement d hNM χ hχ ?_ hmoves
  intro n w
  obtain ⟨b, hb, hbn⟩ := n.property
  have hbsecond : (e (imageActor d I hIM b)).2 = 1 := hb
  have hbactor : d.actor ⟨n, hNM n.property⟩ =
      f (e (imageActor d I hIM b)).1 := by
    have hnb : (⟨n, hNM n.property⟩ : M) = ⟨b, hIM b.property⟩ :=
      Subtype.ext hbn.symm
    rw [hnb]
    change (imageActor d I hIM b : OrthogonalActor) =
      (e.symm ((e (imageActor d I hIM b)).1, 1) : OrthogonalActor)
    congr 1
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext rfl hbsecond
  rw [hbactor]
  exact hinv _ w

/-- A nonidentity cubic centralizing a definite plane has nonidentity
projections to both fully moving Omega factors. Only the two genuine
full-displacement conclusions of 15.3.53(1) are used. -/
theorem cubic_omega_projections_ne_one (d : NaturalOrthogonalAction M V) (I : Subgroup G) (hIM : I ≤ M)
    (e : d.image I ≃* OrthogonalPlaneActor × OrthogonalPlaneActor)
    (hfirst : ⁅V, firstOmegaFactor d I hIM e⁆ = V)
    (hsecond : ⁅V, secondOmegaFactor d I hIM e⁆ = V)
    (i : OrthogonalPlaneIndex) (a : I) (hpow : a ^ 3 = 1)
    (hne : d.actor ⟨a, hIM a.property⟩ ≠ 1)
    (hcentral : (a : G) ∈ centralizer (d.plane i : Set G)) :
    (e (imageActor d I hIM a)).1 ≠ 1 ∧
      (e (imageActor d I hIM a)).2 ≠ 1 := by
  refine ⟨?_, second_projection_ne_one d I hIM e hfirst i a hpow hne hcentral⟩
  exact second_projection_ne_one d I hIM
    (e.trans MulEquiv.prodComm)
    hsecond i a hpow hne hcentral

namespace NaturalQuotientPair
variable {d : NaturalOrthogonalAction M V}
  {I P : Subgroup G} {hIM : I ≤ M} {hIP : I ≤ normalizer (P : Set G)}
  [(V.subgroupOf P).Normal]

/-- The marked cubic has nontrivial projections in the factor coordinates of
the actual natural quotient pair. This discharges the projection premises
of the quotient centralizer reduction. -/
theorem cubic_projections_ne_one (r : NaturalQuotientPair d I P hIM hIP)
    (i : OrthogonalPlaneIndex) (a : I) (hpow : a ^ 3 = 1)
    (hne : d.actor ⟨a, hIM a.property⟩ ≠ 1)
    (hcentral : (a : G) ∈ centralizer (d.plane i : Set G)) :
    (r.factors (imageActor d I hIM a)).1 ≠ 1 ∧
      (r.factors (imageActor d I hIM a)).2 ≠ 1 :=
  cubic_omega_projections_ne_one d I hIM r.factors r.first_moves r.second_moves
    i a hpow hne hcentral

end NaturalQuotientPair
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
