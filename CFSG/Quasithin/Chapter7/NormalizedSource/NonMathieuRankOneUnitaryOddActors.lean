module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Semilinearity
public import Theory.Representation.BinaryOffender.PerfectNormalizer
public import Theory.Representation.SemilinearFixedPointCentralizer
public import Theory.Representation.FiniteFieldSemilinearDisplacement
public import Theory.LinearAlgebra.OddDeterminantOneDisplacement
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement

/-!
# Odd-prime actors on the marked natural unitary module

Semilinear coverage of the full special-unitary group, followed by Schur's
lemma on the original irreducible module, constructs the coefficient action
of its entire binary linear normalizer. H.0.1 bounds every nontrivial odd
field actor. If an odd-prime actor moves fewer than 4s binary dimensions,
its coefficient is trivial and its displacement over the original field
has rank one. Its determinant is nontrivial by the odd transvection lemma.
All identifications retain the full central cover and literal operators.

The companion `NonMathieuRankOneUnitaryDisplacement` excludes these
reflections using the actual SQTK cover and A.1.31(1). That cover is essential:
the displacement bound is false for the full linear normalizer.
Source: Aschbacher--Smith H.0.1--H.2, printed pp.377--378.
-/
public noncomputable section
open Subgroup Matrix Representation Representation.BinaryOffender BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterK.RankOne
variable {X E F : Type*} [Group X]
  [AddCommGroup E] [Module (ZMod 2) E]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) X E} {Q : Subgroup X}
  (M : UnitaryModel J ρ Q)

@[expose] noncomputable def unitaryNormalizerCoordinates :
    Representation (ZMod 2) (linearNormalizer (ρ.comp Q.subtype)) (Fin 3 → F) :=
  M.coordinates.conjRingEquiv.toMonoidHom.comp (normalizerRepresentation (ρ.comp Q.subtype))

omit [Finite F] in
/-- The full normalizer operator in the original marked coordinates. -/
theorem unitaryNormalizerCoordinates_apply
    (a : linearNormalizer (ρ.comp Q.subtype)) (v : Fin 3 → F) :
    unitaryNormalizerCoordinates M a v =
      M.coordinates (normalizerRepresentation (ρ.comp Q.subtype) a (M.coordinates.symm v)) := rfl

private noncomputable def fieldOperator (σ : F ≃+* F) (u : GL (Fin 3) F) :
    (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F) :=
  ({ AddEquiv.piCongrRight (fun _ : Fin 3 => σ.toAddEquiv) with
    map_smul' := fun c v => by ext i; exact ZMod.map_smul σ c (v i) } :
    (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F)).trans
    ((GeneralLinearGroup.toLin u).toLinearEquiv.restrictScalars (ZMod 2))

omit [Finite F] in
private theorem fieldOperator_smul (σ : F ≃+* F) (u : GL (Fin 3) F)
    (c : F) (v : Fin 3 → F) :
    fieldOperator σ u (c • v) = σ c • fieldOperator σ u v := by
  change u.val *ᵥ (σ ∘ (c • v)) = σ c • (u.val *ᵥ (σ ∘ v))
  have he : σ ∘ (c • v) = σ c • (σ ∘ v) := by ext i; exact σ.map_mul c (v i)
  rw [he, Matrix.mulVec_smul]

/-- The full binary normalizer has a genuine compatible coefficient action. -/
theorem unitaryNormalizer_semilinear
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp Q.subtype))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2^s)^2) (hconj : ∀ x : F, J.conj x = x^(2^s))
    (a : linearNormalizer (ρ.comp Q.subtype)) :
    ∃ σ : F ≃+* F, ∀ c v,
      unitaryNormalizerCoordinates M a (c • v) =
        σ c • unitaryNormalizerCoordinates M a v := by
  let τ : Representation (ZMod 2) Q E := ρ.comp Q.subtype
  let e := PerfectNormalizer.imageEquiv τ (hf.comp Q.subtype_injective)
  let α : MulAut Q := MulAut.congr e.symm ((actionImage τ).normalizerMonoidHom a)
  let β : MulAut J.specialSubgroup := MulAut.congr M.groupEquiv α
  obtain ⟨σ,u,hu⟩ := HermitianForm.EvenSemilinear.special_semilinear_coverage
    J hJ hs hcard hconj β
  let μ := M.coordinateAction.comp Q.subtype
  let er : Representation.Equiv τ μ := Representation.Equiv.mk M.coordinates (by
    intro q
    apply LinearMap.ext
    intro v
    exact (M.coordinateAction_apply q v).symm)
  let : IsIrreducible μ := (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv er)).mp hi
  have hτ (q : Q) (c : F) (v : Fin 3 → F) : μ q (c • v) = c • μ q v := by
    change M.coordinateAction (q : X) (c • v) = c • M.coordinateAction (q : X) v
    rw [M.coordinateAction_natural,M.coordinateAction_natural,Matrix.mulVec_smul]
  have ha (q : Q) (v : Fin 3 → F) :
      unitaryNormalizerCoordinates M a (μ q v) = μ (α q) (unitaryNormalizerCoordinates M a v) := by
    have he : τ.asGroupHom (α q) = a.val * τ.asGroupHom q * a.val⁻¹ :=
      congrArg Subtype.val (e.apply_symm_apply ((actionImage τ).normalizerMonoidHom a (e q)))
    have hh := congrArg (fun z : (Module.End (ZMod 2) E)ˣ => z.val (a.val.val (M.coordinates.symm v))) he
    change τ (α q) (a.val.val (M.coordinates.symm v)) =
      a.val.val (τ q (a.val.inv (a.val.val (M.coordinates.symm v)))) at hh
    have hinv : ∀ w, a.val.inv (a.val.val w) = w :=
      fun w => LinearMap.congr_fun a.val.inv_val w
    rw [hinv] at hh
    change M.coordinates (a.val.val (M.coordinates.symm (M.coordinates (τ q (M.coordinates.symm v))))) =
      M.coordinates (τ (α q) (M.coordinates.symm (M.coordinates (a.val.val (M.coordinates.symm v)))))
    simpa only [M.coordinates.symm_apply_apply] using congrArg M.coordinates hh.symm
  have hB (q : Q) (v : Fin 3 → F) :
      fieldOperator σ u.val (μ q v) = μ (α q) (fieldOperator σ u.val v) := by
    have hg : (M.groupEquiv (α q)).val =
        u.val * GeneralLinearGroup.map σ.toRingHom (M.groupEquiv q).val * u.val⁻¹ := by
      simpa only [β, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hu (M.groupEquiv q)
    change u.val.val *ᵥ (σ ∘ (M.coordinateAction (q : X) v)) =
      M.coordinateAction (α q : X) (u.val.val *ᵥ (σ ∘ v))
    rw [M.coordinateAction_natural,M.coordinateAction_natural]
    have hm : σ ∘ ((M.groupEquiv q).val.val *ᵥ v) =
        (GeneralLinearGroup.map σ.toRingHom (M.groupEquiv q).val).val *ᵥ (σ ∘ v) := by
      ext i
      exact σ.toRingHom.map_mulVec _ v i
    rw [hm,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
    have he : u.val * GeneralLinearGroup.map σ.toRingHom (M.groupEquiv q).val =
        (M.groupEquiv (α q)).val * u.val := by rw [hg]; group
    exact congrArg (fun B : GL (Fin 3) F => B.val *ᵥ (σ ∘ v)) he
  exact ⟨σ, FiniteSchurIntertwiner.semilinear_of_intertwining μ hτ α
    (unitaryNormalizerCoordinates M a) (fieldOperator σ u.val) σ ha hB
    (fieldOperator_smul σ u.val)⟩

/-- Nontrivial odd-prime field actors satisfy the H.2 displacement bound. -/
theorem unitaryNormalizer_field_displacement
    (π : linearNormalizer (ρ.comp Q.subtype) →* (F ≃+* F))
    (hπ : ∀ a c v, unitaryNormalizerCoordinates M a (c • v) =
      π a c • unitaryNormalizerCoordinates M a v)
    {s p : ℕ} (hcard : Nat.card F = (2^s)^2) (hp : p.Prime) (ho : Odd p)
    (a : linearNormalizer (ρ.comp Q.subtype)) (ha : orderOf a = p) (hne : π a ≠ 1) :
    4*s ≤ fixedCodim (normalizerRepresentation (ρ.comp Q.subtype)) (zpowers a) := by
  have hd : orderOf (π a) ∣ p := ha ▸ orderOf_map_dvd π a
  have horder : orderOf (π a) = p :=
    ((Nat.dvd_prime hp).mp hd).resolve_left (fun h => hne (orderOf_eq_one_iff.mp h))
  have hb := FiniteFieldSemilinearDisplacement.two_thirds_le_fixedCodim
    (unitaryNormalizerCoordinates M) hp ho a ha (π a) horder (hπ a)
  rw [UnitaryModel.field_finrank hcard] at hb
  have hc := fixedCodim_map_equivariant (normalizerRepresentation (ρ.comp Q.subtype))
    (unitaryNormalizerCoordinates M) (MonoidHom.id _) M.coordinates
    (fun _ _ => by simp [unitaryNormalizerCoordinates]) (zpowers a)
  simp only [Subgroup.map_id] at hc
  rw [hc]
  simp only [Module.finrank_pi, Fintype.card_fin] at hb
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource


namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterK.RankOne
variable {X E F : Type*} [Group X]
  [AddCommGroup E] [Module (ZMod 2) E]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) X E} {Q : Subgroup X}
  (M : UnitaryModel J ρ Q)

theorem unitaryNormalizer_exists_coefficient
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp Q.subtype))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2^s)^2) (hconj : ∀ x : F, J.conj x = x^(2^s)) :
    ∃ π : linearNormalizer (ρ.comp Q.subtype) →* (F ≃+* F),
      ∀ a c v, unitaryNormalizerCoordinates M a (c • v) =
        π a c • unitaryNormalizerCoordinates M a v :=
  ⟨SemilinearFixedPointCentralizer.coefficient _
      (unitaryNormalizer_semilinear M hf hi hJ hs hcard hconj),
    SemilinearFixedPointCentralizer.coefficient_smul _ _⟩

/-- A small odd-prime actor is a genuine linear reflection, with its order,
displacement rank and nontrivial determinant retained. -/
theorem unitaryNormalizer_small_odd_reflection
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp Q.subtype))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2^s)^2) (hconj : ∀ x : F, J.conj x = x^(2^s))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (a : linearNormalizer (ρ.comp Q.subtype)) (ha : orderOf a = p)
    (hsmall : fixedCodim (normalizerRepresentation (ρ.comp Q.subtype)) (zpowers a) < 4*s) :
    ∃ e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      (∀ v, e v = unitaryNormalizerCoordinates M a v) ∧ orderOf e = p ∧
      Module.finrank F (LinearMap.range (e.toLinearMap - LinearMap.id)) = 1 ∧
      e.det ≠ 1 := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨π,hπ⟩ := unitaryNormalizer_exists_coefficient M hf hi hJ hs hcard hconj
  have hπa : π a = 1 := by
    by_contra hn
    exact (not_le_of_gt hsmall) (unitaryNormalizer_field_displacement M π hπ hcard hp ho a ha hn)
  let τ := unitaryNormalizerCoordinates M
  let e₂ := LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom a)
  let e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) :=
    { e₂.toAddEquiv with
      map_smul' := fun c v => by
        change τ a (c • v) = c • τ a v
        simpa only [hπa,RingAut.one_apply] using hπ a c v }
  have he (v : Fin 3 → F) : e v = τ a v := rfl
  have hτ : Function.Injective τ := by
    intro x y h
    apply Subtype.ext
    apply Units.ext
    exact M.coordinates.conjRingEquiv.injective h
  have heone : e ≠ 1 := by
    intro hh
    have haone : a = 1 := hτ (by
      apply LinearMap.ext
      intro v
      rw [map_one]
      change τ a v = v
      rw [←he,hh]
      rfl)
    exact hp.ne_one (by simpa [haone] using ha.symm)
  have heorder : orderOf e = p := by
    have hinj : Function.Injective
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → F)).toMonoidHom.comp
          τ.asGroupHom) :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).injective.comp
        (fun _ _ h => hτ (congrArg Units.val h))
    have ho₂ := (orderOf_injective _ hinj a).trans ha
    have he₂ : e.restrictScalars (ZMod 2) = e₂ := by ext; rfl
    let r : ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) →*
        ((Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F)) :=
      { toFun := LinearEquiv.restrictScalars (ZMod 2)
        map_one' := by ext; rfl
        map_mul' := fun _ _ => by ext; rfl }
    have hr : orderOf (e.restrictScalars (ZMod 2)) = orderOf e :=
      orderOf_injective r (LinearEquiv.restrictScalars_injective (ZMod 2)) e
    rw [he₂] at hr
    exact hr.symm.trans ho₂
  have hc : fixedCodim (normalizerRepresentation (ρ.comp Q.subtype)) (zpowers a) =
      fixedCodim τ (zpowers a) := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant
      (normalizerRepresentation (ρ.comp Q.subtype)) τ (MonoidHom.id _) M.coordinates
      (fun _ _ => by simp [τ,unitaryNormalizerCoordinates]) (zpowers a)
  have hr : fixedCodim τ (zpowers a) =
      (2*s) * Module.finrank F (LinearMap.range (e.toLinearMap - LinearMap.id)) := by
    have hδ : τ a = (e.restrictScalars (ZMod 2)).toLinearMap := by
      apply LinearMap.ext
      intro v
      rfl
    rw [fixedCodim_zpowers_eq_displacement_rank,hδ]
    simpa only [UnitaryModel.field_finrank hcard] using
      (QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) e)
  have hlt : Module.finrank F (LinearMap.range (e.toLinearMap - LinearMap.id)) < 2 := by
    rw [hc,hr] at hsmall
    nlinarith
  have hpos : 0 < Module.finrank F (LinearMap.range (e.toLinearMap - LinearMap.id)) := by
    by_contra! hn
    have hz := (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hn))
    have heq : e.toLinearMap - LinearMap.id = 0 := LinearMap.range_eq_bot.mp hz
    apply heone
    exact LinearEquiv.toLinearMap_injective (sub_eq_zero.mp heq)
  refine ⟨e,he,heorder,by omega,?_⟩
  intro hd
  exact (not_le_of_gt hlt) (e.two_le_displacement_of_odd_det_one heone (heorder ▸ ho) hd)
end CFSG.Quasithin.Chapter7.NormalizedSource
