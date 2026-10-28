module

public import Theory.Representation.BinaryPermutation
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry

/-!
# Six-letter flags and their residual images

The canonical finite calculations and Sylow transport supply the image
bridges for the corrected application of B.3.4 in 13.2.2(4). The concrete pair stabilizer, or its alternating intersection,
has residual image `K`, the embedded `A₄`. If the acting subgroup's image
contains `D0` and is contained in the pair stabilizer, its commutator with
this residual image is all of `K`. The ambient homomorphism need not be
surjective, and the source stabilizer need not be normal.

The plane residual has ambient two-core D0. A common marking constructed
from the actual Sylow and natural-module subspaces identifies the source
line residual and plane residual core without offender assumptions. The
separate stable-family argument must still supply the offender containment
used by the commutator application.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Notation 13.2.1 and Lemma 13.2.2(4), printed pp.877–878; compare B.3.4,
printed p.85. The finite canonical calculations are re-exported separately
from any offender or stable-family hypothesis.
-/

public section

namespace CFSG.Quasithin.ChapterB.Flags

open Subgroup Theory.SpecificGroups.SymmetricSix.BinaryFlags

variable {G : Type*} [Group G] [Finite G]

/-- Transport the residual through a homomorphism onto a canonical pair
stabilizer or its alternating intersection. -/
theorem residual_image_eq_K (M : Subgroup G) (f : G →* S)
    (hM : M.map f = H1 ∨ M.map f = L1) :
    ((pResidual 2 M).map M.subtype).map f = K := by
  rw [map_embedded_pResidual]
  rcases hM with hM | hM
  · rw [hM, residual_H1]
  · rw [hM, residual_L1]

/-- The commutator conclusion needed by 13.2.2(4), once its stable-family
argument supplies the two image containments. -/
theorem commutator_residual_image_eq_K (M J : Subgroup G) (f : G →* S)
    (hM : M.map f = H1 ∨ M.map f = L1)
    (hD : D0 ≤ J.map f) (hJ : J.map f ≤ H1) :
    (⁅(pResidual 2 M).map M.subtype, J⁆).map f = K := by
  rw [map_commutator, residual_image_eq_K M f hM]
  exact commutator_eq_K_of_between K (J.map f) le_rfl K_le_H1 hD hJ


open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

/-- The marked plane residual's two-core is the literal even swap group,
after the actual residual-image map. No injectivity of the source map is needed. -/
theorem plane_residual_image_core (M : Subgroup G) (f : G →* S)
    (hM : M.map f = H2 ∨ M.map f = L2) :
    (((pResidual 2 M).map M.subtype).map f).pCoreIn 2 = D0 := by
  rw [map_embedded_pResidual]
  rcases hM with hM | hM
  · rw [hM, H2_residual_core_eq_D0]
  · rw [hM, L2_residual_core_eq_D0]

private theorem conjugate_intersection (H P : Subgroup S) (g : H) :
    (H ⊓ P).map (MulAut.conj (g : S)).toMonoidHom =
      H ⊓ P.map (MulAut.conj (g : S)).toMonoidHom := by
  have hc : H.map (MulAut.conj (g : S)).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer g.property)
  rw [map_inf _ _ _ (MulAut.conj (g : S)).injective, hc]

/-- The source's line residual under any marking in the actual overgroup. -/
theorem line_residual_of_marking (H : Subgroup S) (hH : alternatingGroup (Fin 6) ≤ H)
    (g : H) :
    let M := H ⊓ flagStabilizer (move (g : S) canonicalLine)
    (pResidual 2 M).map M.subtype = K.map (MulAut.conj (g : S)).toMonoidHom := by
  have hm : (H ⊓ H1).map (MulAut.conj (g : S)).toMonoidHom =
      H ⊓ flagStabilizer (move (g : S) canonicalLine) := by
    rw [conjugate_intersection, flagStabilizer_move, flagStabilizer_line]
  dsimp only
  rw [← hm, ← map_embedded_pResidual,
    residual_eq_K_of_between (H ⊓ H1)
      (le_inf (inf_le_right.trans hH) K_le_H1) inf_le_right]

/-- The plane residual's two-core under the same marking; the residual
and its intrinsic core are embedded before comparison with D0. -/
theorem plane_residual_core_of_marking (H : Subgroup S)
    (hH : alternatingGroup (Fin 6) ≤ H) (g : H) :
    let M := H ⊓ flagStabilizer (move (g : S) canonicalPlane)
    ((pResidual 2 M).map M.subtype).pCoreIn 2 =
      D0.map (MulAut.conj (g : S)).toMonoidHom := by
  have hm : (H ⊓ H2).map (MulAut.conj (g : S)).toMonoidHom =
      H ⊓ flagStabilizer (move (g : S) canonicalPlane) := by
    rw [conjugate_intersection, flagStabilizer_move, flagStabilizer_plane]
  dsimp only
  rw [← hm, ← map_embedded_pResidual,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj (g : S)).injective,
    plane_residual_core_of_between (H ⊓ H2)
      (le_inf (inf_le_right.trans hH) inf_le_left) inf_le_right]

/-- The corrected commutator calculation survives every permutation marking. -/
theorem commutator_marked_residual (g : S) (J : Subgroup S)
    (hD : D0.map (MulAut.conj g).toMonoidHom ≤ J)
    (hJ : J ≤ H1.map (MulAut.conj g).toMonoidHom) :
    ⁅K.map (MulAut.conj g).toMonoidHom, J⁆ = K.map (MulAut.conj g).toMonoidHom := by
  let e := MulAut.conj g
  let J0 := J.map e.symm.toMonoidHom
  have hback : J0.map e.toMonoidHom = J := by simp [J0, map_map]
  have hD0 : D0 ≤ J0 := by
    have h := map_mono (f := e.symm.toMonoidHom) hD
    simpa [J0, e, map_map] using h
  have hJ0 : J0 ≤ H1 := by
    have h := map_mono (f := e.symm.toMonoidHom) hJ
    simpa [J0, e, map_map] using h
  change ⁅K.map e.toMonoidHom, J⁆ = K.map e.toMonoidHom
  rw [← hback, ← map_commutator,
    commutator_eq_K_of_between K J0 le_rfl K_le_H1 hD0 hJ0]

/-- A concrete application to the literal source flags. The Sylow and natural
module hypotheses construct the common marking and discharge every geometric
premise of the residual calculations. The stable-family owner supplies the
separate offender containment used by `commutator_marked_residual`. -/
theorem source_flag_residual_data (H : Subgroup S)
    (hH : alternatingGroup (Fin 6) ≤ H) (T : Sylow 2 H)
    (P Q : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) (hQ : Module.finrank (ZMod 2) Q = 2)
    (hPi : ∀ x ∈ (T : Subgroup H).map H.subtype, move x P = P)
    (hQi : ∀ x ∈ (T : Subgroup H).map H.subtype, move x Q = Q) :
    ∃ g : H, P = move (g : S) canonicalLine ∧ Q = move (g : S) canonicalPlane ∧
      (pResidual 2 ↥(H ⊓ flagStabilizer P)).map (H ⊓ flagStabilizer P).subtype =
        K.map (MulAut.conj (g : S)).toMonoidHom ∧
      ((pResidual 2 ↥(H ⊓ flagStabilizer Q)).map (H ⊓ flagStabilizer Q).subtype).pCoreIn 2 =
        D0.map (MulAut.conj (g : S)).toMonoidHom := by
  obtain ⟨g, rfl, rfl⟩ := sylow_flag_of_between H hH T P Q hP hQ hPi hQi
  exact ⟨g, rfl, rfl, line_residual_of_marking H hH g, plane_residual_core_of_marking H hH g⟩

end CFSG.Quasithin.ChapterB.Flags
