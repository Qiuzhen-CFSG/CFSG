module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.Action
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Theory.Representation.OrthogonalFourPlusMatrix.LowRank
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.SingularExclusions
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.Representation.OrthogonalFourPlusMatrix.InvariantQuadratic
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowFixed

/-!
# The orthogonal inspection in Lemma 14.4.6(b)

The input is the literal faithful H/O₂(H) action on U/Z(U), with the image
of O²(H) identified equivariantly with the natural Ω₄⁺(4) action. The
remaining earlier-source inputs are a Sylow two-subgroup T of H, normalization
of the actual V₂ by T, and binary dimension one of its actual quotient image.
These are the marked-line data of 12.8.2 and Hypothesis 14.3.10. No low-rank
classification, field linearity, determinant preservation or singular marking
is an input.

The additive commutant recovers F₄. The full binary normalizer therefore acts
semilinearly, and a nontrivial field twist moves at least four dimensions.
A nonidentity actor of binary rank at most two is thus field-linear of field
rank one and binary rank two. Invariant quadratic forms make each such
involution a determinant isometry. Sylow conjugacy then makes the actual
T-fixed quotient line singular over F₄. Finally the literal quotient-action
lemma `orthogonal_line_not_le_moved` excludes that line from displacement.

This argument uses the normal natural layer in 14.4.2(3) and works for its
full binary normalizer. It therefore applies with the stated W^{g*} marking
without choosing a representative for its rank-four component-swapping
involution. In particular all field actors and their products with component
interchange are covered by the same semilinear rank bound.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 14.4.2(3)
and 14.4.6(b), printed pp.1006--1008. This module does not concern the
subsequent orthogonal elimination in 14.4.9.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open Module Subgroup ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
variable {H V : Type*} [Group H] (U : Subgroup H) [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual star actor inherits the full-normalizer rank calculation in determinant coordinates. -/
theorem SourceAction.orthogonal_matrix_lowRank
    (d : SourceAction H U V)
    (K : Subgroup (H ⧸ pCore 2 H)) [K.Normal]
    (κ : K ≃* Binary.G) (e : V ≃ₗ[ZMod 2] Binary.V)
    (hmodel : ∀ (g : K) v, e (d.representation g v) = Binary.action (κ g) (e v))
    (a : H ⧸ pCore 2 H) (ha : a ≠ 1) (hr : d.movedRank a ≤ 2) :
    ∃ t : Binary.V ≃ₗ[Binary.F] Binary.V,
      (∀ v, e (d.representation a v) = t (e v)) ∧
      t.restrictScalars (ZMod 2) ∈ normalizer
        (Binary.linearAction.range : Set (Binary.V ≃ₗ[ZMod 2] Binary.V)) ∧
      finrank Binary.F (LinearMap.range (t.toLinearMap - LinearMap.id)) = 1 ∧
      d.movedRank a = 2 := by
  let τ : Representation (ZMod 2) (H ⧸ pCore 2 H) Binary.V :=
    (LinearEquiv.conjRingEquiv e).toMonoidHom.comp d.representation
  let ρ : (H ⧸ pCore 2 H) →* (Binary.V ≃ₗ[ZMod 2] Binary.V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Binary.V).toMonoidHom.comp τ.asGroupHom
  have hρ (g : H ⧸ pCore 2 H) (M : Binary.V) : ρ g M = e (d.representation g (e.symm M)) := rfl
  have himage : K.map ρ = Binary.linearAction.range := by
    ext t
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨κ ⟨g, hg⟩, ?_⟩
      apply LinearEquiv.ext
      intro M
      rw [hρ, hmodel ⟨g, hg⟩, e.apply_symm_apply]
      rfl
    · rintro ⟨g, rfl⟩
      refine ⟨(κ.symm g : K), (κ.symm g).property, ?_⟩
      apply LinearEquiv.ext
      intro M
      rw [hρ, hmodel, κ.apply_symm_apply, e.apply_symm_apply]
      rfl
  have hnorm : ρ a ∈ normalizer (Binary.linearAction.range : Set (Binary.V ≃ₗ[ZMod 2] Binary.V)) := by
    rw [← himage]
    apply Subgroup.le_normalizer_map ρ
    apply Subgroup.mem_map_of_mem
    rw [Subgroup.normalizer_eq_top]
    trivial
  have he (v : V) : e (d.representation a v) = ρ a (e v) := by
    rw [hρ, e.symm_apply_apply]
  have hdim := d.movedRank_eq_of_equivariant a e (ρ a).toLinearMap he
  have hne : ρ a ≠ 1 := by
    intro hh
    apply ha
    apply d.faithful
    rw [map_one]
    ext v
    apply e.injective
    rw [he, hh]
    rfl
  obtain ⟨t, ht, hF, hb⟩ := Binary.low_rank_nonidentity (ρ a) hnorm (hdim ▸ hr) hne
  refine ⟨t, ?_, ?_, hF, hdim.trans hb⟩
  · intro v
    rw [he, ← ht]
    rfl
  · rw [ht]
    exact hnorm

/-- Every source low-rank involution is an F₄-linear isometry of field moved rank one.
The model equivalence is to the genuine elementary orthogonal carrier. -/
theorem SourceAction.orthogonal_involution_lowRank
    (d : SourceAction H U V)
    (K : Subgroup (H ⧸ pCore 2 H)) [K.Normal]
    (κ : K ≃* OmegaPlus 2 Binary.F) (e : V ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (hmodel : ∀ (g : K) v, e (d.representation g v) =
      subgroupNatural (OmegaPlus 2 Binary.F) (κ g) (e v))
    (a : H ⧸ pCore 2 H) (ha : orderOf a = 2) (hr : d.movedRank a ≤ 2) :
    ∃ t : VectorD 2 Binary.F ≃ₗ[Binary.F] VectorD 2 Binary.F,
      (∀ v, e (d.representation a v) = t (e v)) ∧
      (∀ v, formD 2 Binary.F (t v) = formD 2 Binary.F v) ∧
      finrank Binary.F (LinearMap.range (t.toLinearMap - LinearMap.id)) = 1 ∧
      d.movedRank a = 2 := by
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  let E : V ≃ₗ[ZMod 2] Binary.V := e.trans Binary.binaryCoordinates
  have hmatrix (g : K) (v : V) : E (d.representation g v) = Binary.action (κm g) (E v) := by
    change Binary.binaryCoordinates (e (d.representation g v)) = _
    rw [hmodel]
    obtain ⟨b, hb⟩ := elementaryEquiv.surjective (κ g)
    have hκ : κm g = b := by
      change elementaryEquiv.symm (κ g) = b
      rw [← hb, elementaryEquiv.symm_apply_apply]
    rw [← hb, hκ]
    exact toOrthogonal_coordinates b (e v)
  have ha' : a ≠ 1 := by intro hh; simp [hh] at ha
  obtain ⟨s, hs, hnorm, _, hb⟩ := d.orthogonal_matrix_lowRank U K κm E hmatrix a ha' hr
  have ha2 : a * a = 1 := by simpa only [ha, pow_two] using pow_orderOf_eq_one a
  have hs2 (M : Binary.V) : s (s M) = M := by
    obtain ⟨v, rfl⟩ := E.surjective M
    rw [← hs, ← hs]
    have hact : d.representation a (d.representation a v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, ha2, map_one]
      rfl
    rw [hact]
  have hpres := Binary.field_involution_preserves_det s hnorm hs2
  let t := (ClassicalOrthogonal.FourPlusMatrix.coordinates (F := Binary.F)).trans (s.trans ClassicalOrthogonal.FourPlusMatrix.coordinates.symm)
  have ht (v : V) : e (d.representation a v) = t (e v) := by
    apply (ClassicalOrthogonal.FourPlusMatrix.coordinates (F := Binary.F)).injective
    change Binary.binaryCoordinates (e (d.representation a v)) =
      ClassicalOrthogonal.FourPlusMatrix.coordinates
        (ClassicalOrthogonal.FourPlusMatrix.coordinates.symm
          (s (ClassicalOrthogonal.FourPlusMatrix.coordinates (e v))))
    rw [ClassicalOrthogonal.FourPlusMatrix.coordinates.apply_symm_apply]
    exact hs v
  have htform (v : VectorD 2 Binary.F) : formD 2 Binary.F (t v) = formD 2 Binary.F v := by
    rw [← coordinates_det, ← coordinates_det]
    change (ClassicalOrthogonal.FourPlusMatrix.coordinates
      (ClassicalOrthogonal.FourPlusMatrix.coordinates.symm
        (s (ClassicalOrthogonal.FourPlusMatrix.coordinates v)))).det = _
    rw [ClassicalOrthogonal.FourPlusMatrix.coordinates.apply_symm_apply, hpres]
  refine ⟨t, ht, htform, ?_, hb⟩
  have hdim := QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) t
  rw [← d.movedRank_eq_of_equivariant a e (t.restrictScalars (ZMod 2)).toLinearMap ht,
    hb, Binary.finrank_field] at hdim
  omega
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open Module Subgroup ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
variable {H V : Type*} [Group H] {U : Subgroup H} [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V]

private theorem nonzero_vector_in_line (d : SourceAction H U V) (V₂ : Subgroup H)
    (hdim : finrank (ZMod 2) (d.image V₂) = 1) :
    ∃ s : U, (s : H) ∈ V₂ ∧ d.vector s ≠ 0 := by
  by_contra! hh
  have hbot : d.image V₂ = ⊥ := by
    apply le_bot_iff.mp
    apply Submodule.span_le.mpr
    rintro v ⟨u, hu, rfl⟩
    exact (Submodule.mem_bot (ZMod 2)).mpr (hh u hu)
  rw [hbot] at hdim
  simp at hdim

private theorem fixed_vector_of_normalized_line (d : SourceAction H U V)
    (V₂ : Subgroup H) (hdim : finrank (ZMod 2) (d.image V₂) = 1)
    (s : U) (hs : (s : H) ∈ V₂) (hs0 : d.vector s ≠ 0)
    (t : H) (ht : t ∈ normalizer (V₂ : Set H)) :
    d.representation (QuotientGroup.mk' (pCore 2 H) t) (d.vector s) = d.vector s := by
  have hmem : d.vector (MulAut.conjNormal t s) ∈ d.image V₂ := by
    apply d.vector_mem_image
    exact (Subgroup.mem_normalizer_iff.mp ht (s : H)).mp hs
  have hne : d.vector (MulAut.conjNormal t s) ≠ 0 := by
    rw [d.conjugation]
    let a := QuotientGroup.mk' (pCore 2 H) t
    let f := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
      (d.representation.asGroupHom a)
    exact fun hh => hs0 (f.injective (hh.trans f.map_zero.symm))
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim
    (show (⟨d.vector s, d.vector_mem_image V₂ s hs⟩ : d.image V₂) ≠ 0 from
      fun he => hs0 (congrArg Subtype.val he))
    (⟨d.vector (MulAut.conjNormal t s), hmem⟩ : d.image V₂)
  have hc' : c • d.vector s = d.vector (MulAut.conjNormal t s) := congrArg Subtype.val hc
  fin_cases c
  · change (0 : ZMod 2) • d.vector s = d.vector (MulAut.conjNormal t s) at hc'
    exact False.elim (hne (by simpa only [zero_smul] using hc'.symm))
  · change (1 : ZMod 2) • d.vector s = d.vector (MulAut.conjNormal t s) at hc'
    simpa only [one_smul, d.conjugation] using hc'.symm

/-- The actual distinguished binary line lies in a singular F₄-point. Its
fixedness is derived from Sylow normalization and its binary dimension. -/
theorem SourceAction.orthogonal_singular_line [Finite H]
    (d : SourceAction H U V)
    (K : Subgroup (H ⧸ pCore 2 H)) [K.Normal]
    (κ : K ≃* OmegaPlus 2 Binary.F) (e : V ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (hmodel : ∀ (g : K) v, e (d.representation g v) =
      subgroupNatural (OmegaPlus 2 Binary.F) (κ g) (e v))
    (T : Sylow 2 H) (V₂ : Subgroup H)
    (hnorm : (T : Subgroup H) ≤ normalizer (V₂ : Set H))
    (hdim : finrank (ZMod 2) (d.image V₂) = 1) :
    ∃ s : U, (s : H) ∈ V₂ ∧ e (d.vector s) ≠ 0 ∧
      formD 2 Binary.F (e (d.vector s)) = 0 ∧
      (d.image V₂).map e.toLinearMap ≤
        (Submodule.span Binary.F {e (d.vector s)}).restrictScalars (ZMod 2) := by
  obtain ⟨s, hs, hs0⟩ := nonzero_vector_in_line d V₂ hdim
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal K
  have hfix (k : K) (hk : k ∈ P) : d.representation k (d.vector s) = d.vector s := by
    change k ∈ (P : Subgroup K) at hk
    rw [hP] at hk
    change (k : H ⧸ pCore 2 H) ∈ (T : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) at hk
    obtain ⟨t, ht, he⟩ := hk
    rw [← he]
    exact fixed_vector_of_normalized_line d V₂ hdim s hs hs0 t (hnorm ht)
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  let E := e.trans Binary.binaryCoordinates
  have hmatrix (g : K) (v : V) : E (d.representation g v) = Binary.action (κm g) (E v) := by
    change Binary.binaryCoordinates (e (d.representation g v)) = _
    rw [hmodel]
    obtain ⟨b, hb⟩ := elementaryEquiv.surjective (κ g)
    have hκ : κm g = b := by
      change elementaryEquiv.symm (κ g) = b
      rw [← hb, elementaryEquiv.symm_apply_apply]
    rw [← hb, hκ]
    exact toOrthogonal_coordinates b (e v)
  have hsing : (E (d.vector s)).det = 0 := by
    apply Binary.sylow_fixed_singular (P.mapSurjective (f := κm.toMonoidHom) κm.surjective)
    intro g hg
    change g ∈ (P : Subgroup K).map κm.toMonoidHom at hg
    obtain ⟨k, hk, rfl⟩ := hg
    change Binary.action (κm k) (E (d.vector s)) = E (d.vector s)
    rw [← hmatrix, hfix k hk]
  have hes0 : e (d.vector s) ≠ 0 := fun hh => hs0 (e.injective (hh.trans e.map_zero.symm))
  refine ⟨s, hs, hes0, ?_, ?_⟩
  · exact (coordinates_det (e (d.vector s))).symm.trans hsing
  · rintro w ⟨v, hv, rfl⟩
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim
      (show (⟨d.vector s, d.vector_mem_image V₂ s hs⟩ : d.image V₂) ≠ 0 from
        fun hh => hs0 (congrArg Subtype.val hh)) (⟨v, hv⟩ : d.image V₂)
    have hc' : c • d.vector s = v := congrArg Subtype.val hc
    have he : c • e (d.vector s) = e v := by
      simpa only [map_smul] using congrArg e hc'
    change e v ∈ (Submodule.span Binary.F {e (d.vector s)}).restrictScalars (ZMod 2)
    rw [← he]
    exact ((Submodule.span Binary.F {e (d.vector s)}).restrictScalars (ZMod 2)).smul_mem c
      (Submodule.mem_span_singleton_self _)

/-- Source 14.4.6(b), on the literal residual image and central quotient.
The earlier marked-line inputs yield both the singular point and the
exclusion from the actual involution displacement. -/
theorem SourceAction.orthogonal_inspection [Finite H]
    (d : SourceAction H U V)
    (κ : ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))) ≃* OmegaPlus 2 Binary.F)
    (e : V ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (hmodel : ∀ (g : (pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))) v,
      e (d.representation g v) = subgroupNatural (OmegaPlus 2 Binary.F) (κ g) (e v))
    (T : Sylow 2 H) (V₂ : Subgroup H)
    (hnorm : (T : Subgroup H) ≤ normalizer (V₂ : Set H))
    (hdim : finrank (ZMod 2) (d.image V₂) = 1)
    (a : H ⧸ pCore 2 H) (ha : orderOf a = 2) (hr : d.movedRank a ≤ 2) :
    d.movedRank a = 2 ∧
      (∃ p : Submodule Binary.F (VectorD 2 Binary.F), finrank Binary.F p = 1 ∧
        (d.image V₂).map e.toLinearMap ≤ p.restrictScalars (ZMod 2) ∧
        ∀ v ∈ p, formD 2 Binary.F v = 0) ∧
      ¬ d.image V₂ ≤ d.moved a := by
  let K := (pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))
  let : K.Normal := (inferInstance : (pResidual 2 H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  obtain ⟨t, ht, htform, _, hb⟩ := d.orthogonal_involution_lowRank U K κ e hmodel a ha hr
  obtain ⟨s, hs, hs0, hsing, hline⟩ := d.orthogonal_singular_line K κ e hmodel T V₂ hnorm hdim
  refine ⟨hb, ?_, d.orthogonal_line_not_le_moved U Binary.finrank_field e a t ht htform hr
    V₂ s hs hs0 hsing⟩
  refine ⟨Submodule.span Binary.F {e (d.vector s)}, finrank_span_singleton hs0, hline, ?_⟩
  intro v hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [QuadraticMap.map_smul, hsing, smul_zero]
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore