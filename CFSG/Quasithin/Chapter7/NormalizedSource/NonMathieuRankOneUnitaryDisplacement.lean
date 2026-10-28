module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneUnitaryOddActors
public import Theory.SpecificGroups.SU3.LinearReflectionObstruction
public import Theory.Representation.BinaryOffender.InnerNormalizerActors
/-!
# H.2 for the original covered unitary action

The coefficient argument reduces a small odd-prime displacement to a linear
reflection. Restrict the original covering group to the field-linear part of
its binary image. The marked full SU₃ lies in that image, so orthogonal
reflection coordinates and A.1.31(1) give a contradiction. The final transport
uses the actual component surjection and the complete ambient action marking.
No rank bound is asserted for an arbitrary quotient or full linear normalizer.

Source: Aschbacher--Smith H.0.1--H.2, printed pp.377--378.
-/
public section
open Subgroup Matrix Representation Representation.BinaryOffender BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterK.RankOne
variable {X E F : Type*} [Group X]
  [AddCommGroup E] [Module (ZMod 2) E]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) X E} {Q : Subgroup X}

private def restrictLinearHom : ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) →*
    ((Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F)) where
  toFun := LinearEquiv.restrictScalars (ZMod 2)
  map_one' := by ext; rfl
  map_mul' := fun _ _ => by ext; rfl

private def binaryMatrixHom : GL (Fin 3) F →* (Module.End (ZMod 2) (Fin 3 → F))ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → F)).symm.toMonoidHom.comp
    (restrictLinearHom.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F)).toMonoidHom.comp
        GeneralLinearGroup.toLin.toMonoidHom))

omit [Finite F] in
private theorem binaryMatrixHom_injective : Function.Injective (binaryMatrixHom (F := F)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → F)).symm.injective.comp
    ((LinearEquiv.restrictScalars_injective (ZMod 2)).comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F)).injective.comp
        GeneralLinearGroup.toLin.injective))

/-- H.2 with rank retained on the actual cover of the marked normalizer image. -/
theorem unitary_normalizer_odd_displacement_of_cover
    (M : UnitaryModel J ρ Q)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp Q.subtype))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2^s)^2) (hconj : ∀ x : F, J.conj x = x^(2^s))
    {K : Type*} [Group K] [Finite K]
    (f : K →* linearNormalizer (ρ.comp Q.subtype))
    (hinner : ∀ q : Q, normalizerEmbedding (ρ.comp Q.subtype) q ∈ f.range)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hrank : primeRank p K ≤ 2)
    (a : linearNormalizer (ρ.comp Q.subtype)) (ha : orderOf a = p) (haim : a ∈ f.range) :
    4*s ≤ fixedCodim (normalizerRepresentation (ρ.comp Q.subtype)) (zpowers a) := by
  by_contra! hsmall
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨e,he,heorder,hr,hd⟩ := unitaryNormalizer_small_odd_reflection
    M hf hi hJ hs hcard hconj hp ho a ha hsmall
  let sigma : Representation (ZMod 2) Q E := ρ.comp Q.subtype
  let U := (unitaryNormalizerCoordinates M).asGroupHom
  let r := binaryMatrixHom (F := F)
  let S := GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  have hSact (v : Fin 3 → F) : S.val *ᵥ v = e v := LinearMap.toMatrix'_mulVec e.toLinearMap v
  have hRS : r S = U a := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact (hSact v).trans (he v)
  have hRQ (q : Q) : r (M.groupEquiv q).val = U (normalizerEmbedding (ρ.comp Q.subtype) q) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change (M.groupEquiv q).val.val *ᵥ v =
      unitaryNormalizerCoordinates M (normalizerEmbedding (ρ.comp Q.subtype) q) v
    rw [unitaryNormalizerCoordinates_apply]
    change (M.groupEquiv q).val.val *ᵥ v = M.coordinates (ρ (q : X) (M.coordinates.symm v))
    simpa only [M.coordinates.apply_symm_apply] using (M.intertwines q (M.coordinates.symm v)).symm
  have hN : ∀ Y : J.specialSubgroup, S*Y.val*S⁻¹ ∈ J.specialSubgroup := by
    intro Y
    let q := M.groupEquiv.symm Y
    have hqin : sigma.asGroupHom q ∈ actionImage (ρ.comp Q.subtype) := ⟨q,rfl⟩
    obtain ⟨q',hq'⟩ := (mem_normalizer_iff.mp a.property _).mp hqin
    have heq : normalizerEmbedding (ρ.comp Q.subtype) q' =
        a * normalizerEmbedding (ρ.comp Q.subtype) q * a⁻¹ := Subtype.ext hq'
    have heq' : r (M.groupEquiv q').val = r (S*Y.val*S⁻¹) := by
      rw [hRQ,heq]
      simp only [map_mul,map_inv]
      rw [hRS]
      have hy : Y = M.groupEquiv q := (M.groupEquiv.apply_symm_apply Y).symm
      rw [hy,hRQ]
    exact (binaryMatrixHom_injective heq') ▸ (M.groupEquiv q').property
  have hSorder : orderOf S = p := by
    have hh := orderOf_injective
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F)).toMonoidHom.comp
        GeneralLinearGroup.toLin.toMonoidHom)
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F)).injective.comp
        GeneralLinearGroup.toLin.injective) S
    have hSe : (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F))
        (GeneralLinearGroup.toLin S) = e := by
      rw [show GeneralLinearGroup.toLin S = LinearMap.GeneralLinearGroup.ofLinearEquiv e from GeneralLinearGroup.toLin.apply_symm_apply _]
      rfl
    change orderOf ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F))
      (GeneralLinearGroup.toLin S)) = orderOf S at hh
    rw [hSe] at hh
    exact hh.symm.trans heorder
  have hSmap : Matrix.toLin' S.val = e.toLinearMap :=
    congrArg Units.val (GeneralLinearGroup.toLin.apply_symm_apply (LinearMap.GeneralLinearGroup.ofLinearEquiv e))
  have hdet : GeneralLinearGroup.det S = e.det := by
    apply Units.ext
    rw [LinearEquiv.coe_det,←hSmap,LinearMap.det_toLin']
    rfl
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj
  have hnconj : ∃ z : F, J.conj z ≠ z := by
    have hne := J.conj_ne_one_of_card s hs hcard hfixed
    by_contra! he
    apply hne
    exact RingEquiv.ext he
  apply UnitaryThree.no_linear_reflection_in_injective_image J hJ hnconj (2^s)
    hcard hfixed r binaryMatrixHom_injective (U.comp f) hrank ho
      ?_ S ?_ hSorder hN (hSmap ▸ hr) (hdet ▸ hd)
  · intro Y
    obtain ⟨k,hk⟩ := hinner (M.groupEquiv.symm Y)
    refine ⟨k,?_⟩
    change U (f k) = r Y.val
    rw [hk,←hRQ,M.groupEquiv.apply_symm_apply]
  · obtain ⟨k,hk⟩ := haim
    exact ⟨k,by change U (f k) = r S; rw [hk,hRS]⟩
end CFSG.Quasithin.Chapter7.NormalizedSource

namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterK.RankOne
variable {X E F A W K B : Type*} [Group X]
  [AddCommGroup E] [Module (ZMod 2) E]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [Group K] [Finite K] [Group B]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) X E} {Q : Subgroup X}

/-- Transport H.2 using the literal component surjection, action marking,
and original rank-two covering group. -/
theorem unitary_odd_fixedCodim_of_ambient_marking
    (M : UnitaryModel J ρ Q)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp Q.subtype))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2^s)^2) (hconj : ∀ x : F, J.conj x = x^(2^s))
    (τ : Representation (ZMod 2) A W)
    (j : A →* linearNormalizer (ρ.comp Q.subtype)) (hj : Function.Injective j)
    (C : E ≃ₗ[ZMod 2] W)
    (hC : ∀ a v, C (normalizerRepresentation (ρ.comp Q.subtype) (j a) v) = τ a (C v))
    (f : K →* A) (hfs : Function.Surjective f)
    (b : B →* Q) (hb : Function.Surjective b) (i : B →* K)
    (hB : ∀ l v, C (ρ (b l : X) v) = τ (f (i l)) (C v))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hrank : primeRank p K ≤ 2)
    (a : A) (ha : orderOf a = p) : 4*s ≤ fixedCodim τ (zpowers a) := by
  have hinner (q : Q) : normalizerEmbedding (ρ.comp Q.subtype) q ∈ (j.comp f).range := by
    obtain ⟨l,rfl⟩ := hb q
    refine ⟨i l,?_⟩
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply C.injective
    exact (hC (f (i l)) v).trans (hB l v).symm
  have hcoord (a : A) (v : W) :
      C.symm (τ a v) = normalizerRepresentation (ρ.comp Q.subtype) (j a) (C.symm v) := by
    apply C.injective
    rw [C.apply_symm_apply,hC,C.apply_symm_apply]
  have hc := fixedCodim_map_equivariant τ (normalizerRepresentation (ρ.comp Q.subtype))
    j C.symm hcoord (zpowers a)
  rw [MonoidHom.map_zpowers] at hc
  rw [hc]
  apply unitary_normalizer_odd_displacement_of_cover M hf hi hJ hs hcard hconj
    (j.comp f) hinner hp ho hrank (j a) ((orderOf_injective j hj a).trans ha)
  obtain ⟨k,rfl⟩ := hfs a
  exact ⟨k,rfl⟩
end CFSG.Quasithin.Chapter7.NormalizedSource
