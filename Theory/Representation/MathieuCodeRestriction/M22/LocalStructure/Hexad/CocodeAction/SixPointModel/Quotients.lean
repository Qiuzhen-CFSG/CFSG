module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel.LinearIdentification

/-!
# The actual alternating and symmetric hexad quotients

The eight-coordinate action of the native octad stabilizer has image A8.
An even permutation of the six remaining coordinates extends by fixing the
marked pair, and hence lifts through the native M22 embedding. An arbitrary
six-coordinate permutation extends to an even octad permutation by exchanging
the marked pair exactly when its sign is negative. Conversely, fixing both
pair points preserves the sign of the six-coordinate restriction.

Thus the actual inner and outer coordinate images are A6 and S6. The first
isomorphism theorem retains the quotient maps, and the earlier H.14
kernel-image comparison identifies the kernels with the intrinsic two-cores
inside the respective stabilizers. That comparison alone remains an explicit
premise of the intrinsic quotient equivalences; neither image equality has
an extra premise.

Source: Aschbacher--Smith, H.14.3(3) and the proof of H.15.2(2),
printed pp.397--399, combined manuscript of 1 March 2004.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode.Hexad.CocodeAction.SixPointModel
noncomputable section

private def coordinatesInOctad : H ≃ {i : O.val // i.val ∈ coordinates} where
  toFun i := ⟨inOctad i, i.property⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def extendCoordinates (s : Equiv.Perm H) : Equiv.Perm O.val :=
  s.extendDomain coordinatesInOctad

private lemma extendCoordinates_apply (s : Equiv.Perm H) (i : H) :
    extendCoordinates s (inOctad i) = inOctad (s i) :=
  Equiv.Perm.extendDomain_apply_image s coordinatesInOctad i

private lemma extendCoordinates_fixed (s : Equiv.Perm H) (i : O.val)
    (hi : i.val ∉ coordinates) : extendCoordinates s i = i :=
  Equiv.Perm.extendDomain_apply_not_subtype s coordinatesInOctad hi

private lemma extendCoordinates_sign (s : Equiv.Perm H) :
    Equiv.Perm.sign (extendCoordinates s) = Equiv.Perm.sign s :=
  Equiv.Perm.sign_extendDomain s coordinatesInOctad

private lemma pair_of_not_coordinates (i : O.val) (hi : i.val ∉ coordinates) :
    i.val = 0 ∨ i.val = 9 := by
  have hp : i.val ∈ m22Pair := by
    by_contra hp
    exact hi (Finset.mem_sdiff.mpr ⟨i.property, hp⟩)
  simpa [m22Pair] using hp

private lemma inner_octad_eq_extension (g : m22InnerHexadStabilizer O) :
    CocodeOctad.coordinateAction O (octadHom m22ToPairStabilizer g) =
      extendCoordinates (innerCoordinateAction g) := by
  apply Equiv.ext
  intro i
  by_cases hi : i.val ∈ coordinates
  · change CocodeOctad.coordinateAction O (octadHom m22ToPairStabilizer g)
        (inOctad ⟨i.val, hi⟩) =
        extendCoordinates (innerCoordinateAction g) (inOctad ⟨i.val, hi⟩)
    rw [extendCoordinates_apply]
    rfl
  · rw [extendCoordinates_fixed _ i hi]
    apply Subtype.ext
    change (m22Embedding g.val).val i.val = i.val
    rcases pair_of_not_coordinates i hi with h | h
    · rw [h]
      exact m22Embedding_fixed_zero g.val
    · rw [h]
      exact m22Embedding_fixed_nine g.val

private lemma lift_even_octad (s : Equiv.Perm O.val) (hs : s ∈ alternatingGroup O.val) :
    ∃ g : octadStabilizer O, CocodeOctad.coordinateAction O g = s := by
  have hr : s ∈ (CocodeOctad.coordinateAction O).range := by
    rwa [CocodeOctad.coordinateAction_range]
  exact hr

/-- The native inner hexad action has exactly the even six-coordinate permutations. -/
lemma innerCoordinateAction_range : innerCoordinateAction.range = alternatingGroup H := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have h : CocodeOctad.coordinateAction O (octadHom m22ToPairStabilizer g) ∈
        alternatingGroup O.val := by
      rw [← CocodeOctad.coordinateAction_range]
      exact ⟨octadHom m22ToPairStabilizer g, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup, inner_octad_eq_extension,
      extendCoordinates_sign] at h
    exact Equiv.Perm.mem_alternatingGroup.mpr h
  · intro s hs
    obtain ⟨g, hg⟩ := lift_even_octad (extendCoordinates s)
      (Equiv.Perm.mem_alternatingGroup.mpr
        ((extendCoordinates_sign s).trans (Equiv.Perm.mem_alternatingGroup.mp hs)))
    have h0 : g.val • (0 : Fin 24) = 0 :=
      congrArg Subtype.val ((Equiv.congr_fun hg anchor).trans
        (extendCoordinates_fixed s anchor (by decide +kernel)))
    have h9 : g.val • (9 : Fin 24) = 9 :=
      congrArg Subtype.val ((Equiv.congr_fun hg partner).trans
        (extendCoordinates_fixed s partner (by decide +kernel)))
    have hm : g.val ∈ m22Embedding.range := by
      rw [m22Embedding_range]
      exact ⟨h0, h9⟩
    obtain ⟨u, hu⟩ := hm
    have huO : u ∈ m22InnerHexadStabilizer O := by
      change m22Embedding u ∈ octadStabilizer O
      rw [hu]
      exact g.property
    refine ⟨⟨u, huO⟩, ?_⟩
    apply Equiv.ext
    intro i
    apply Subtype.ext
    change (m22Embedding u).val i.val = (s i).val
    rw [hu]
    exact congrArg Subtype.val ((Equiv.congr_fun hg (inOctad i)).trans
      (extendCoordinates_apply s i))

private def evenExtension (s : Equiv.Perm H) : Equiv.Perm O.val :=
  if Equiv.Perm.sign s = 1 then extendCoordinates s
  else extendCoordinates s * Equiv.swap anchor partner

private lemma evenExtension_even (s : Equiv.Perm H) :
    evenExtension s ∈ alternatingGroup O.val := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  have hab : anchor ≠ partner := by decide +kernel
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · simp [evenExtension, h, extendCoordinates_sign]
  · simp [evenExtension, h, Equiv.Perm.sign_mul, extendCoordinates_sign,
      Equiv.Perm.sign_swap hab]

private lemma evenExtension_apply (s : Equiv.Perm H) (i : H) :
    evenExtension s (inOctad i) = inOctad (s i) := by
  have h0 : inOctad i ≠ anchor := by
    intro he
    exact (Finset.mem_sdiff.mp i.property).2 (by
      have h := congrArg Subtype.val he
      change i.val = 0 at h
      simp [m22Pair, h])
  have h9 : inOctad i ≠ partner := by
    intro he
    exact (Finset.mem_sdiff.mp i.property).2 (by
      have h := congrArg Subtype.val he
      change i.val = 9 at h
      simp [m22Pair, h])
  simp only [evenExtension]
  split
  · exact extendCoordinates_apply s i
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h0 h9]
    exact extendCoordinates_apply s i

private lemma evenExtension_pair (s : Equiv.Perm H) (i : O.val) (hi : i.val ∈ m22Pair) :
    (evenExtension s i).val ∈ m22Pair := by
  have h0 : extendCoordinates s anchor = anchor :=
    extendCoordinates_fixed s anchor (by decide +kernel)
  have h9 : extendCoordinates s partner = partner :=
    extendCoordinates_fixed s partner (by decide +kernel)
  have hip : i = anchor ∨ i = partner := by
    simpa [m22Pair, Subtype.ext_iff, anchor, partner] using hi
  rcases hip with rfl | rfl <;>
    simp only [evenExtension] <;> split <;>
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, h0, h9] <;>
    decide +kernel

/-- Allowing exchange of the marked pair gives every six-coordinate permutation. -/
lemma outerCoordinateAction_range : outerCoordinateAction.range = ⊤ := by
  apply MonoidHom.range_eq_top.mpr
  intro s
  obtain ⟨g, hg⟩ := lift_even_octad (evenExtension s) (evenExtension_even s)
  have hp : g.val ∈ m22PairStabilizer := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    have hiO : i ∈ O.val := m22Pair_le_sourceOctad hi
    have he := congrArg Subtype.val (Equiv.congr_fun hg ⟨i, hiO⟩)
    change g.val.val i ∈ m22Pair
    rw [show g.val.val i = (evenExtension s ⟨i, hiO⟩).val from he]
    exact evenExtension_pair s _ hi
  let u : m22PairStabilizer := ⟨g.val, hp⟩
  have huO : u ∈ m22OuterHexadStabilizer O := g.property
  refine ⟨⟨u, huO⟩, ?_⟩
  apply Equiv.ext
  intro i
  apply Subtype.ext
  change g.val.val i.val = (s i).val
  exact congrArg Subtype.val ((Equiv.congr_fun hg (inOctad i)).trans
    (evenExtension_apply s i))

/-- The first isomorphism theorem for the actual inner coordinate action. -/
def innerQuotientAlternatingEquiv :
    (m22InnerHexadStabilizer O ⧸ innerCoordinateAction.ker) ≃* alternatingGroup H :=
  (QuotientGroup.quotientKerEquivRange innerCoordinateAction).trans
    (MulEquiv.subgroupCongr innerCoordinateAction_range)

/-- The first isomorphism theorem for the actual outer coordinate action. -/
def outerQuotientSymmetricEquiv :
    (m22OuterHexadStabilizer O ⧸ outerCoordinateAction.ker) ≃* Equiv.Perm H :=
  QuotientGroup.quotientKerEquivOfSurjective outerCoordinateAction
    (MonoidHom.range_eq_top.mp outerCoordinateAction_range)

@[simp] lemma innerQuotientAlternatingEquiv_mk (g : m22InnerHexadStabilizer O) :
    (innerQuotientAlternatingEquiv (QuotientGroup.mk g) : Equiv.Perm H) =
      innerCoordinateAction g := by
  rfl

@[simp] lemma outerQuotientSymmetricEquiv_mk (g : m22OuterHexadStabilizer O) :
    outerQuotientSymmetricEquiv (QuotientGroup.mk g) = outerCoordinateAction g := by
  rfl

/-- The inner kernel is relative to the hexad stabilizer; only the earlier
H.14 comparison with the octad pointwise kernel is required. -/
lemma innerCoordinateAction_ker
    (hK : (m22InnerHexadKernel O).map m22Embedding = octadPointwiseKernel O) :
    innerCoordinateAction.ker =
      (m22InnerHexadKernel O).subgroupOf (m22InnerHexadStabilizer O) := by
  apply coordinateAction_ker (f := m22ToPairStabilizer)
  · intro x y h
    exact m22Embedding_injective (congrArg Subtype.val h)
  · exact hK

/-- The same relative kernel comparison for the setwise pair group. -/
lemma outerCoordinateAction_ker
    (hK : (m22OuterHexadKernel O).map m22PairStabilizer.subtype = octadPointwiseKernel O) :
    outerCoordinateAction.ker =
      (m22OuterHexadKernel O).subgroupOf (m22OuterHexadStabilizer O) :=
  coordinateAction_ker Function.injective_id hK

/-- In the inner stabilizer the relative intrinsic kernel is its own two-core. -/
lemma innerHexadKernel_subgroupOf :
    (m22InnerHexadKernel O).subgroupOf (m22InnerHexadStabilizer O) =
      pCore 2 (m22InnerHexadStabilizer O) := by
  apply Subgroup.comap_map_eq_self
  simp

/-- In the outer stabilizer the relative intrinsic kernel is its own two-core. -/
lemma outerHexadKernel_subgroupOf :
    (m22OuterHexadKernel O).subgroupOf (m22OuterHexadStabilizer O) =
      pCore 2 (m22OuterHexadStabilizer O) := by
  apply Subgroup.comap_map_eq_self
  simp

lemma innerCoordinateAction_ker_eq_pCore
    (hK : (m22InnerHexadKernel O).map m22Embedding = octadPointwiseKernel O) :
    innerCoordinateAction.ker = pCore 2 (m22InnerHexadStabilizer O) :=
  (innerCoordinateAction_ker hK).trans innerHexadKernel_subgroupOf

lemma outerCoordinateAction_ker_eq_pCore
    (hK : (m22OuterHexadKernel O).map m22PairStabilizer.subtype = octadPointwiseKernel O) :
    outerCoordinateAction.ker = pCore 2 (m22OuterHexadStabilizer O) :=
  (outerCoordinateAction_ker hK).trans outerHexadKernel_subgroupOf

/-- The inner quotient by its intrinsic two-core acts as A6 on the actual hexad.
The premise is precisely the earlier H.14 kernel-image comparison. -/
def innerIntrinsicQuotientAlternatingEquiv
    (hK : (m22InnerHexadKernel O).map m22Embedding = octadPointwiseKernel O) :
    (m22InnerHexadStabilizer O ⧸ pCore 2 (m22InnerHexadStabilizer O)) ≃* alternatingGroup H :=
  (QuotientGroup.quotientMulEquivOfEq (innerCoordinateAction_ker_eq_pCore hK).symm).trans
    innerQuotientAlternatingEquiv

/-- The outer quotient by its intrinsic two-core acts as S6 on the actual hexad.
No normality in the ambient M22 automorphism group is asserted. -/
def outerIntrinsicQuotientSymmetricEquiv
    (hK : (m22OuterHexadKernel O).map m22PairStabilizer.subtype = octadPointwiseKernel O) :
    (m22OuterHexadStabilizer O ⧸ pCore 2 (m22OuterHexadStabilizer O)) ≃* Equiv.Perm H :=
  (QuotientGroup.quotientMulEquivOfEq (outerCoordinateAction_ker_eq_pCore hK).symm).trans
    outerQuotientSymmetricEquiv

@[simp] lemma innerIntrinsicQuotientAlternatingEquiv_mk
    (hK : (m22InnerHexadKernel O).map m22Embedding = octadPointwiseKernel O)
    (g : m22InnerHexadStabilizer O) :
    (innerIntrinsicQuotientAlternatingEquiv hK (QuotientGroup.mk g) : Equiv.Perm H) =
      innerCoordinateAction g := by
  rfl

@[simp] lemma outerIntrinsicQuotientSymmetricEquiv_mk
    (hK : (m22OuterHexadKernel O).map m22PairStabilizer.subtype = octadPointwiseKernel O)
    (g : m22OuterHexadStabilizer O) :
    outerIntrinsicQuotientSymmetricEquiv hK (QuotientGroup.mk g) =
      outerCoordinateAction g := by
  rfl

end
end MathieuCode.Hexad.CocodeAction.SixPointModel
