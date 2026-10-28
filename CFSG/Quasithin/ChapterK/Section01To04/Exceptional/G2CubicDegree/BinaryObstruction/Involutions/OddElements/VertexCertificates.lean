module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.Representatives
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.VertexCertificates.MatrixRanks

/-!
# Certified odd-word displacement on the vertex factors

The five degree-fourteen diagonal blocks have rank at least ten for `AB-I`
and at least twelve for `A-B`. Transport through `adaptedFlagCoordinates`
identifies these with the operators on the literal successive quotients.
The inverse-free displacement identity then proves `VertexSamples` for the
published words `a*b` and `a*b⁻¹`.

The final consumer supplies these numerical samples to `vertexBounds_of_samples`,
retaining cyclic-conjugacy coverage as its independent group-theoretic premise.
Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3,
pp.10–11. This module proves the vertex calculation, with no module-catalogue
or conjugacy assumption in `vertexSamples`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
open Representation Representation.BinaryOffender
open G2DerivedPermutationFiltration.VertexCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

private theorem rank_eq_of_coordinates {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {n : ℕ} (e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (f : V →ₗ[ZMod 2] V) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (h : ∀ v, e (f v) = M.mulVec (e v)) :
    Module.finrank (ZMod 2) (LinearMap.range f) = M.rank := by
  have hm : M.mulVecLin = (e.toLinearMap.comp f).comp e.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    change M.mulVec v = e (f (e.symm v))
    simpa only [e.apply_symm_apply] using (h (e.symm v)).symm
  rw [Matrix.rank, hm, LinearMap.range_comp_of_range_eq_top _ e.symm.range,
    LinearMap.range_comp, e.finrank_map_eq]

private theorem samples_of_matrix_ranks (i : Fin 2) (t : Factor i)
    (hthree : 10 ≤ (factorMatrix i t 0 * factorMatrix i t 1 - 1).rank)
    (hseven : 12 ≤ (factorMatrix i t 0 - factorMatrix i t 1).rank) :
    RepresentativeBounds (vertexFactorRepresentation i t) regularWord sevenWord := by
  let e := (adaptedFlagCoordinates i).coordinates t
  have hg (j : Fin 2) (v : VertexFactorSpace i t) :
      e (vertexFactorRepresentation i t (FreeGroup.of j) v) =
        (factorMatrix i t j).mulVec (e v) :=
    (adaptedFlagCoordinates i).generator_coordinates t j v
  apply representativeBounds_of_generator_ranks
    (vertexFactorRepresentation i t) (FreeGroup.of 0) (FreeGroup.of 1)
  · rw [rank_eq_of_coordinates e _ (factorMatrix i t 0 * factorMatrix i t 1 - 1) ?_]
    · exact hthree
    intro v
    change e (vertexFactorRepresentation i t (FreeGroup.of 0)
      (vertexFactorRepresentation i t (FreeGroup.of 1) v) - v) = _
    rw [map_sub, hg, hg, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.one_mulVec]
  · rw [rank_eq_of_coordinates e _ (factorMatrix i t 0 - factorMatrix i t 1) ?_]
    · exact hseven
    intro v
    change e (vertexFactorRepresentation i t (FreeGroup.of 0) v -
      vertexFactorRepresentation i t (FreeGroup.of 1) v) = _
    rw [map_sub, hg, hg, Matrix.sub_mulVec]

/-- The two odd-word lower bounds on all five degree-fourteen literal quotients.
The certificate retains both vertex flags and uses their actual coordinate maps. -/
theorem vertexSamples : VertexSamples := by
  intro i t ht
  have hc : (i = 0 ∧ t.val = 0) ∨ (i = 0 ∧ t.val = 4) ∨
      (i = 0 ∧ t.val = 7) ∨ (i = 1 ∧ t.val = 1) ∨ (i = 1 ∧ t.val = 6) :=
    (by decide +kernel : ∀ (i : Fin 2) (t : Factor i), degree i t = 14 →
      (i = 0 ∧ t.val = 0) ∨ (i = 0 ∧ t.val = 4) ∨ (i = 0 ∧ t.val = 7) ∨
      (i = 1 ∧ t.val = 1) ∨ (i = 1 ∧ t.val = 6)) i t ht
  rcases hc with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · have he : t = ⟨0, by decide⟩ := Fin.ext h
    subst t
    exact samples_of_matrix_ranks _ _ VertexCertificates.b00.ranks.1
      VertexCertificates.b00.ranks.2
  · have he : t = ⟨4, by decide⟩ := Fin.ext h
    subst t
    exact samples_of_matrix_ranks _ _ VertexCertificates.b04.ranks.1
      VertexCertificates.b04.ranks.2
  · have he : t = ⟨7, by decide⟩ := Fin.ext h
    subst t
    exact samples_of_matrix_ranks _ _ VertexCertificates.b07.ranks.1
      VertexCertificates.b07.ranks.2
  · have he : t = ⟨1, by decide⟩ := Fin.ext h
    subst t
    exact samples_of_matrix_ranks _ _ VertexCertificates.b11.ranks.1
      VertexCertificates.b11.ranks.2
  · have he : t = ⟨6, by decide⟩ := Fin.ext h
    subst t
    exact samples_of_matrix_ranks _ _ VertexCertificates.b16.ranks.1
      VertexCertificates.b16.ranks.2

/-- The certified vertex samples discharge the numerical premise of the
odd-displacement assembly. The independent cyclic-conjugacy coverage remains
explicit and is supplied by the source-theorem assembly owner. -/
theorem vertexBounds_of_certified_samples (hcov : ConjugacyCoverage) : VertexBounds :=
  vertexBounds_of_samples hcov vertexSamples

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
