module
public import Theory.SpecificGroups.GL2.OddCoefficientFixedSylow
public import GorensteinWalter.ProjectiveSemilinear

/-!
# Projective Sylow subgroups fixed by an odd field subgroup

Let K be any finite field of odd cardinality and D an odd-order subgroup of
its actual field automorphism group. There are Sylow two-subgroups of both
PSL₂(K) and PGL₂(K) fixed pointwise by every element of D under the existing
coefficient actions. The statement includes the fields of orders three and
nine and keeps the given coefficient subgroup and maps.

The fixed-subfield construction already provides a coefficient-fixed Sylow
of GL₂(K), and its normal-intersection wrapper provides one of the actual
determinant-one subgroup. Map the former through GL₂ → PGL₂. For the latter,
use the canonical determinant-zero-level equivalence with SL₂, followed by
SL₂ → PSL₂. Surjective homomorphisms preserve Sylow subgroups; the projective
coefficient-map equations and the matrix-preserving SL₂ equivalence show
that both images remain pointwise fixed.

This is the linear-model fixed-Sylow input invoked in Alperin--Brauer--
Gorenstein II.3 Proposition 4(iv), article pages 28--29 (PDF pages 29--30),
from Gorenstein--Walter Lemma 3.3(i). It assumes no D-group recognition,
solubility, abstract replacement action, or invariance-to-fixation principle.
-/

namespace GorensteinWalter
open Matrix.GeneralLinearGroup

/-- Actual odd field automorphisms fix suitable PSL2 and PGL2 Sylow subgroups pointwise. -/
public theorem exists_sylow_two_fixed_by_odd_field_subgroup
    (K : Type*) [Field K] [Finite K] (hK : Odd (Nat.card K))
    (D : Subgroup (K ≃+* K)) (hD : Odd (Nat.card D)) :
    ∃ (S : Sylow 2 (PSL2 K)) (T : Sylow 2 (PGL2 K)),
      (∀ (σ : D) (s : S), psl2FieldAut K σ.val s.val = s.val) ∧
      (∀ (σ : D) (t : T), pgl2FieldAut K σ.val t.val = t.val) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_fixed_by_odd_coefficient_subgroup K hK D hD 0 (by simp)
  obtain ⟨Q, hQ⟩ := exists_gl_sylow_fixed_by_odd_coefficient_subgroup K hK D hD
  let e := determinantTwoPowerZeroEquivSL K
  let f : determinantTwoPower K 0 →* PSL2 K :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).comp e.toMonoidHom
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp e.surjective
  let q : GL (Fin 2) K →* PGL2 K := QuotientGroup.mk' (Subgroup.center _)
  let S := P.mapSurjective hf
  let T := Q.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center _))
  refine ⟨S, T, ?_, ?_⟩
  · intro σ s
    obtain ⟨y, hy, he⟩ := s.property
    change f y = s.val at he
    rw [← he]
    change psl2FieldAut K σ.val (QuotientGroup.mk' (Subgroup.center _) (e y)) =
      QuotientGroup.mk' (Subgroup.center _) (e y)
    rw [psl2FieldAut_apply, psl2RingEquiv_mk]
    apply congrArg (QuotientGroup.mk' (Subgroup.center _))
    ext i j
    have he (i j : Fin 2) : (e y).val i j = y.val i j :=
      congrArg (fun g : GL (Fin 2) K => g i j) (determinantTwoPowerZeroEquivSL_toGL K y)
    change σ.val ((e y).val i j) = (e y).val i j
    rw [he]
    exact congrArg (fun g : GL (Fin 2) K => g i j) (hP σ ⟨y,hy⟩)
  · intro σ t
    obtain ⟨y, hy, he⟩ := t.property
    change q y = t.val at he
    rw [← he]
    exact (pgl2FieldAut_apply K σ.val (q y)).trans
      ((pgl2RingEquiv_mk σ.val y).trans (congrArg q (hQ σ ⟨y,hy⟩)))
end GorensteinWalter
