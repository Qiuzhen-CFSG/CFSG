module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverSymplecticGeometry.Seed
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverSymplecticGeometry.Model

/-!
# Geometric preparation of the five-dimensional-cover branch

The source's two-sided H-adjustment is exhibited and preserves the transported
critical pair. Its seed has nontrivial star image and commutator equal to the
transported central line. The precise normalizer intersection of 13.5.5 places
V₃ in M_V^g, hence gives its genuine natural action on V^g. The invariant flag
is identified with the perpendicular flag of the concrete coordinate pairing.
An isometry with only line displacement fixes this perpendicular hyperplane,
contradicting the chosen seed. Thus V₁^g < [V^g,V₃].

Explicit earlier inputs, to be discharged by the source assembly owner:
* H = C_G(z), V₁ = ⟨z⟩ of order two, and V₁ ≤ V₃;
* the genuine transported configuration from F.9, including centralization
  of its transported denominator (the adapter is `Configuration.of_criticalPair`);
* abelianness of U_H from 13.7.2;
* N_G(V₁) ∩ N_G(V₃) ≤ M_V, exactly 13.5.5;
* the actual natural coordinate action of M_V on V from §13.2 and Remark
  13.5.3, including the multiplicative equivalence and conjugation formula;
* the invariant line and hyperplane of Notation 13.2.1, with the standard
  alternating Borel realized in T in those same coordinates.

The line and hyperplane inputs are only dimensions, invariance, containment,
and actual Borel lifts; their orthogonality is proved. Neither a noncommuting
seed, symplectic placement, form preservation nor strict displacement is an
input. No S₆ cover comparison or star-image equality is asserted here.

Source: Aschbacher–Smith, 13.8.7, printed p.949 (PDF p.966).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The complete geometric helper. The new endpoint and both adjustments are
part of the result, and every assertion concerns the same adjusted element. -/
theorem prepare_cover_geometry
    (H T C M V J : Subgroup G) (z g : G)
    (hH : H = centralizer ({z} : Set G))
    (hcard : Nat.card (zpowers z) = 2) (hZC : zpowers z ≤ C)
    (habel : ⁅Source.UH H C, Source.UH H C⁆ = ⊥)
    (hM : normalizer (zpowers z) ⊓ normalizer C ≤ M)
    (cfg : Configuration H C (zpowers z) (Source.QH H) g)
    (a : NaturalAction M V) (f : NaturalFlag a T (zpowers z) C)
    (hHJ : H ≤ J) (hg : g ∈ J) :
    ∃ h ∈ H, ∃ k ∈ H,
      let g' := k⁻¹ * (g * h)
      let A := (zpowers z).conjBy g'
      let B := C.conjBy g'
      let W := V.conjBy g'
      g' ∈ J ∧
      Configuration H C (zpowers z) (Source.QH H) g' ∧
      H.conjBy g' = (H.conjBy g).conjBy k⁻¹ ∧
      (Source.UH H C).conjBy g' = ((Source.UH H C).conjBy g).conjBy k⁻¹ ∧
      (Source.QH H).conjBy g' = ((Source.QH H).conjBy g).conjBy k⁻¹ ∧
      A = ((zpowers z).conjBy g).conjBy k⁻¹ ∧
      normalizer A = H.conjBy g' ∧
      B ≤ H ∧ Source.starImage H B ≠ ⊥ ∧ ⁅B, C⁆ ≠ ⊥ ∧
      ⁅B, C⁆ = A ∧ A ≤ B ∧ B ≤ W ∧
      C ≤ centralizer A ⊓ normalizer B ∧
      centralizer A ⊓ normalizer B ≤ M.conjBy g' ∧
      C ≤ normalizer W ∧
      subspace (a.conjugate g').coordinate B =
        form.orthogonal (subspace (a.conjugate g').coordinate A) ∧
      A < ⁅W, C⁆ := by
  obtain ⟨h, hh, k, hk, cfg', heH, heU, heA, hBH, hs, hn, hc, hAB, hCN, hNM⟩ :=
    choose_seed H C M z g hH hcard hZC habel hM cfg
  let g' := k⁻¹ * (g * h)
  have hQ : H ≤ normalizer (Source.QH H) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hBW : C.conjBy g' ≤ V.conjBy g' := map_mono f.hyperplane_le
  have hCM : C ≤ M.conjBy g' := hCN.trans hNM
  have horth : subspace (a.conjugate g').coordinate (C.conjBy g') =
      form.orthogonal (subspace (a.conjugate g').coordinate ((zpowers z).conjBy g')) := by
    change subspace (conjugateCoordinate a.coordinate g') (C.conjBy g') =
      form.orthogonal (subspace (conjugateCoordinate a.coordinate g') ((zpowers z).conjBy g'))
    rw [subspace_conjugate, subspace_conjugate]
    exact f.orthogonal
  have hline : Module.finrank (ZMod 2)
      (subspace (a.conjugate g').coordinate ((zpowers z).conjBy g')) = 1 := by
    change Module.finrank (ZMod 2)
      (subspace (conjugateCoordinate a.coordinate g') ((zpowers z).conjBy g')) = 1
    rw [subspace_conjugate]
    exact f.line_rank
  exact ⟨h, hh, k, hk, adjusted_mem H J g h k hHJ hg hh hk,
    cfg', heH, heU, double_adjustment_conjugate H _ g h k hQ hh, heA,
    center_normalizer_eq_conjugate_H H z g' hH hcard,
    hBH, hs, hn, hc, hAB, hBW, hCN, hNM, hCM.trans (a.conjugate g').normalizes,
    horth, strict_displacement (a.conjugate g') hCM hBW hline horth hn hc⟩

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverGeometry
end
