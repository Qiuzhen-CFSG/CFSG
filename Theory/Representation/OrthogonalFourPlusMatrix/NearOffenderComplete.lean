module

public import Theory.Representation.OrthogonalFourPlusMatrix.NearOffenderSwap
public import Theory.Representation.OrthogonalFourPlusMatrix.NearOffenderCanonical

/-!
# A rank-two involution in every determinant near-offender

An elementary near-offender has rank one or three. In the absence of a
rank-two operator the rank-three case has a common fixed space equal to
that of an actual inner involution. This space forces all actors to be
field-linear. Conjugating the inner involution to a pair of standard roots
reduces to the pointwise determinant-isometry calculation: absence of a
field-rank-one operator bounds the actor order by four, a contradiction.

The conclusion retains an element of the original subgroup. It supplies
the transvection witness needed by Aschbacher–Smith 9.2.1(2), printed p.730,
from the near-offender calculation H.1.1(2), printed p.378. No identification
of the entire near-offender as a cyclic subgroup is required.
-/

@[expose] public noncomputable section
open Module Matrix Subgroup
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor

local instance : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- An isometry group fixing the full fixed space of a nonidentity inner
involution has order at most four if it contains no rank-one operator. -/
theorem pointwise_inner_card_le_four
    (r : G) (hr2 : r * r = 1) (hr1 : r ≠ 1) (A : Subgroup (V ≃ₗ[F] V))
    (hfix : ∀ a ∈ A, ∀ v, matrixAction r v = v → a v = v)
    (hdet : ∀ a ∈ A, ∀ v, (a v).det = v.det)
    (hno : ∀ a ∈ A, a ≠ 1 → finrank F (LinearMap.range (a.toLinearMap - LinearMap.id)) ≠ 1) :
    Nat.card A ≤ 4 := by
  obtain ⟨s, c, hs1, hs2, hs, hc⟩ := exists_standard_inner_conjugate
    canonicalRoot canonicalRoot_square canonicalRoot_ne_one r hr2 hr1
  let g := matrixHom c
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hcard : Nat.card B = Nat.card A := card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [← hcard]
  apply canonical_pointwise_card_le_four s hs1 hs2 hs B
  · rintro b ⟨a, ha, rfl⟩ v hv
    have hrvc : matrixAction r (g v) = g v := by
      have he : matrixHom r * g = g * matrixHom s := by
        change matrixHom r * matrixHom c = matrixHom c * matrixHom s
        rw [← map_mul, ← map_mul]
        apply congrArg matrixHom
        rw [← hc]
        group
      have hh := LinearEquiv.congr_fun he v
      change matrixAction r (g v) = g (matrixAction s v) at hh
      rw [hv] at hh
      exact hh
    change g⁻¹ (a (g v)) = v
    rw [hfix a ha (g v) hrvc]
    exact g.symm_apply_apply v
  · rintro b ⟨a, ha, rfl⟩ v
    change (g⁻¹ (a (g v))).det = v.det
    have hg1 (x : V) : (g⁻¹ x).det = x.det := by
      change ((matrixHom c)⁻¹ x).det = x.det
      rw [← map_inv]
      exact matrixAction_det c⁻¹ x
    rw [hg1, hdet a ha]
    exact matrixAction_det c v
  · rintro b ⟨a, ha, rfl⟩ hb hd
    have ha1 : a ≠ 1 := by
      intro hh
      apply hb
      rw [hh, map_one]
    apply hno a ha ha1
    have he := Representation.BinaryNormalizerRank.rank_conj g⁻¹ a
    change finrank F (LinearMap.range (((MulAut.conj g⁻¹) a).toLinearMap - LinearMap.id)) =
      finrank F (LinearMap.range (a.toLinearMap - LinearMap.id)) at he
    exact he.symm.trans hd

private theorem exists_rank_two_member
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hnear : fixedCodim (normalizerRepresentation action) A ≤ rank A + 1) :
    ∃ t ∈ A, t ≠ 1 ∧ operatorFixedCodim t.val.val = 2 := by
  by_contra! hno
  let := hA.2
  obtain ⟨hr, hc, hu⟩ := near_offender_uniform_of_no_rank_two A hA hnear hno
  obtain ⟨t, ht, ht1, r, hr1, hr2, htr⟩ :=
    exists_inner_involution_of_rank_ge_three A hA hr.ge
  obtain ⟨f, hfinj, hf⟩ := exists_field_actor_hom A
    (near_offender_field_linear_of_no_rank_two A hA hnear hno)
  have hft (a : A) : (f a).restrictScalars (ZMod 2) =
      LinearMap.GeneralLinearGroup.toLinearEquiv a.val.val := by
    apply LinearEquiv.ext
    intro v
    exact hf a v
  have he : fixedSpace (normalizerRepresentation action) A =
      fixedSpace (normalizerRepresentation action) (zpowers t) := by
    apply fixedSpace_eq_of_fixedCodim_eq _ (zpowers_le.mpr ht)
    rw [fixedCodim_zpowers_eq_displacement_rank, hc]
    exact (hu t ht ht1).symm
  have hb := pointwise_inner_card_le_four r hr2 hr1 f.range (by
      rintro a ⟨b, rfl⟩ v hv
      have hvW : v ∈ fixedSpace (normalizerRepresentation action) A := by
        rw [he, mem_fixedSpace_zpowers_iff]
        change t.val.val v = v
        rw [htr]
        exact hv
      rw [hf]
      exact hvW b)
    (by
      rintro a ⟨b, rfl⟩
      apply field_involution_preserves_det (f b)
      · rw [hft]
        exact normalizer_linearEquiv_mem b.val
      · intro v
        have hb2 : b * b = 1 := by
          apply Subtype.ext
          change b.val * b.val = 1
          simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
            b.val b.property
        have hh : f b * f b = 1 := by rw [← map_mul, hb2, map_one]
        exact LinearEquiv.congr_fun hh v)
    (by
      rintro a ⟨b, rfl⟩ hb hn
      have hb1 : b.val ≠ 1 := by
        intro hh
        have hb' : b = 1 := Subtype.ext hh
        exact hb (by rw [hb', map_one])
      apply hno b.val b.property hb1
      have hd := QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) (f b)
      rw [hft, finrank_field, hn] at hd
      exact hd.trans (by decide))
  have hcard : Nat.card f.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  rw [hcard, hA.card_eq_two_pow_rank, hr] at hb
  omega

/-- Every elementary near-offender on the binary determinant module contains
an involution moving exactly two binary dimensions. The witness belongs to
the original actor, so any ambient Sylow membership is retained. -/
theorem exists_rank_two_involution_of_near_offender
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hnear : fixedCodim (normalizerRepresentation action) A ≤ rank A + 1) :
    ∃ t ∈ A, t ≠ 1 ∧ t * t = 1 ∧ operatorFixedCodim t.val.val = 2 := by
  obtain ⟨t, ht, ht1, htr⟩ := exists_rank_two_member A hA hnear
  let := hA.2
  refine ⟨t, ht, ht1, ?_, htr⟩
  simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht

end ClassicalOrthogonal.FourPlusMatrix.Binary
