module

public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerNonFF
public import Theory.Representation.BinaryOffender.UniformFixedSpace

/-!
# Near-offenders in the binary determinant normalizer

A normalizer operator moving at most three binary dimensions is linear over
F₄, since a nontrivial field twist moves at least four. Its displacement
therefore has even binary dimension. The same scalar restriction controls
common fixed spaces of small elementary actors.

These estimates are used for the field-four tensor branch of
Aschbacher–Smith 9.2.1 and 9.4.5, printed pp.730,737, via the near-offender
calculation in H.1.1, printed p.378.
-/

@[expose] public noncomputable section
open Module Matrix Subgroup
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor

local instance : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- A displacement bound of three still excludes a nontrivial field twist. -/
theorem rank_three_field_linear (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 3) :
    ∀ (c : F) (M : V), t (c • M) = c • t M := by
  obtain ⟨σ, hσ⟩ := normalizer_semilinear t ht
  have hs (c : F) : σ c = c := by
    by_contra hc
    have hb := finrank_le_twice_operatorFixedCodim t.toLinearMap σ.toRingHom ⟨c, hc⟩ hσ
    rw [finrank_binary] at hb
    change 8 ≤ 2 * finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) at hb
    omega
  simpa only [hs] using hσ

/-- The small operator has a field-linear lift with the same literal action. -/
theorem rank_three_field_equiv (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 3) :
    ∃ s : V ≃ₗ[F] V, s.restrictScalars (ZMod 2) = t := by
  let f : V →ₗ[F] V :=
    { toFun := t
      map_add' := t.map_add
      map_smul' := rank_three_field_linear t ht hr }
  exact ⟨LinearEquiv.ofBijective f t.bijective, by apply LinearEquiv.ext; intro M; rfl⟩

/-- There are no operators of binary displacement rank three in the normalizer. -/
theorem rank_le_two_of_rank_le_three (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 3) :
    finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 2 := by
  obtain ⟨s, hs⟩ := rank_three_field_equiv t ht hr
  have hd := QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) s
  rw [hs, finrank_field] at hd
  omega

/-- A scalar-stable binary subspace has even dimension. -/
theorem even_finrank_of_field_stable (W : Submodule (ZMod 2) V)
    (hW : ∀ (c : F) (v : V), v ∈ W → c • v ∈ W) :
    Even (finrank (ZMod 2) W) := by
  let U : Submodule F V :=
    { carrier := W
      zero_mem' := W.zero_mem
      add_mem' := W.add_mem
      smul_mem' := hW }
  have hd := finrank_mul_finrank (ZMod 2) F U
  rw [finrank_field] at hd
  change 2 * finrank F U = finrank (ZMod 2) W at hd
  exact ⟨finrank F U, by omega⟩

/-- Small common fixed codimension is even, since each actor is field-linear. -/
theorem fixedCodim_le_two_of_le_three
    (A : Subgroup (linearNormalizer action))
    (hsmall : fixedCodim (normalizerRepresentation action) A ≤ 3) :
    fixedCodim (normalizerRepresentation action) A ≤ 2 := by
  have he := even_finrank_of_field_stable
    (fixedSpace (normalizerRepresentation action) A) (by
      intro c v hv t
      let e := LinearMap.GeneralLinearGroup.toLinearEquiv t.val.val
      have hr : finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 3 :=
        (operatorFixedCodim_le_fixedCodim (normalizerRepresentation action) A t.property).trans hsmall
      have hh := rank_three_field_linear e (normalizer_linearEquiv_mem t.val) hr c v
      change t.val.val.val (c • v) = c • v
      change t.val.val.val (c • v) = c • t.val.val.val v at hh
      rw [hh]
      exact congrArg (fun w : V => c • w) (hv t))
  obtain ⟨n, hn⟩ := he
  have hd := fixedCodim_add_finrank (normalizerRepresentation action) A
  rw [finrank_binary] at hd
  omega

/-- An elementary subgroup with common fixed codimension at most three is cyclic. -/
theorem rank_le_one_of_fixedCodim_le_three
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim (normalizerRepresentation action) A ≤ 3) : rank A ≤ 1 :=
  rank_le_one_of_fixedCodim_le_two A hA (fixedCodim_le_two_of_le_three A hsmall)

/-- A near-offender has rank one or three; rank two and four cannot occur. -/
theorem near_offender_rank_alternatives
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hnear : fixedCodim (normalizerRepresentation action) A ≤ rank A + 1) :
    rank A = 1 ∨ rank A = 3 := by
  have hr := elementary_normalizer_rank_le_four A hA
  have hp := hA.rank_pos
  by_cases hfour : 4 ≤ rank A
  · have hh := fixedCodim_ge_six_of_rank_ge_four A hA hfour
    omega
  by_cases hthree : 3 ≤ rank A
  · right; omega
  have hs : fixedCodim (normalizerRepresentation action) A ≤ 3 := by omega
  have hh := rank_le_one_of_fixedCodim_le_three A hA hs
  left; omega

/-- Without a rank-two member, the only near-offender alternative has
rank three and all nonidentity members move the same four dimensions. -/
theorem near_offender_uniform_of_no_rank_two
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hnear : fixedCodim (normalizerRepresentation action) A ≤ rank A + 1)
    (hno : ∀ t ∈ A, t ≠ 1 → operatorFixedCodim t.val.val ≠ 2) :
    rank A = 3 ∧ fixedCodim (normalizerRepresentation action) A = 4 ∧
      ∀ t ∈ A, t ≠ 1 → operatorFixedCodim t.val.val = 4 := by
  have hlarge (t : linearNormalizer action) (ht : t ∈ A) (hne : t ≠ 1) :
      4 ≤ operatorFixedCodim t.val.val := by
    by_contra! hn
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv t.val
    have he : e ≠ 1 := by
      intro he
      exact hne (Subtype.ext (Units.ext (congrArg LinearEquiv.toLinearMap he)))
    have hb : finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 3 := by
      change operatorFixedCodim t.val.val ≤ 3
      omega
    have hl := rank_le_two_of_rank_le_three e (normalizer_linearEquiv_mem t) hb
    obtain ⟨_, _, _, hd⟩ := low_rank_nonidentity e (normalizer_linearEquiv_mem t) hl he
    exact hno t ht hne hd
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hb := (hlarge t ht ht1).trans
    (operatorFixedCodim_le_fixedCodim (normalizerRepresentation action) A ht)
  have hr : rank A = 3 := by
    rcases near_offender_rank_alternatives A hA hnear with hh | hh
    · omega
    · exact hh
  have hc : fixedCodim (normalizerRepresentation action) A = 4 := by omega
  exact ⟨hr, hc, fun t ht hn => le_antisymm
    ((operatorFixedCodim_le_fixedCodim (normalizerRepresentation action) A ht).trans hc.le)
    (hlarge t ht hn)⟩

/-- The hypothetical remaining near-offender acts quadratically. -/
theorem near_offender_quadratic_of_no_rank_two
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hnear : fixedCodim (normalizerRepresentation action) A ≤ rank A + 1)
    (hno : ∀ t ∈ A, t ≠ 1 → operatorFixedCodim t.val.val ≠ 2) :
    IsQuadratic (normalizerRepresentation action) A := by
  let := hA.2
  obtain ⟨_, hc, he⟩ := near_offender_uniform_of_no_rank_two A hA hnear hno
  apply isQuadratic_of_common_fixedCodim
  intro t ht hn
  rw [fixedCodim_zpowers_eq_displacement_rank, hc]
  exact (he t ht hn).symm

/-- The rank-three actor contains a specified nonidentity inner involution,
with its actual matrix operator retained. -/
theorem exists_inner_involution_of_rank_ge_three
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A) (hr : 3 ≤ rank A) :
    ∃ t ∈ A, t ≠ 1 ∧ ∃ r : G, r ≠ 1 ∧ r * r = 1 ∧ t.val.val = action r := by
  let := hA.2
  have hpr : 3 ≤ primeRank 2 A := by
    rwa [← Representation.AlternatingFivePairCubicCriterion.rank_eq_primeRank A hA]
  obtain ⟨t, ht, r, hr1, hr2, htr⟩ :=
    Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.faithful_actor_inner
      (alternatingConjugation.comp A.subtype) (alternatingConjugation_elementary_injective A) hpr
  let s := alternatingPairEquiv.symm r
  have hs2 : s * s = 1 := by
    simpa only [s, pow_two, map_mul, map_one] using congrArg alternatingPairEquiv.symm hr2
  have hs1 : s ≠ 1 := by
    intro hh
    apply hr1
    simpa only [s, map_one, MulEquiv.apply_symm_apply] using congrArg alternatingPairEquiv hh
  have ht2 : (t : linearNormalizer action) * t = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (t : linearNormalizer action) t.property
  have hts : normalizerConjugation t = MulAut.conj s := by
    apply (MulAut.congr alternatingPairEquiv).injective
    change alternatingConjugation t = _
    rw [show alternatingConjugation t = MulAut.conj r from htr]
    apply MulEquiv.ext
    intro x
    simp [MulAut.congr, s]
  exact ⟨t, t.property, fun hh => ht (Subtype.ext hh), s, hs1, hs2,
    inner_involution_eq_action t ht2 s hs2 hts⟩

/-- Fixing a nonzero scalar orbit forces the field automorphism to be trivial. -/
theorem normalizer_field_linear_of_fixed_scalar_orbit (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (v : V) (hv : v ≠ 0) (hfix : ∀ c : F, t (c • v) = c • v) :
    ∀ (c : F) (M : V), t (c • M) = c • t M := by
  obtain ⟨σ, hσ⟩ := normalizer_semilinear t ht
  have hvfix : t v = v := by simpa using hfix 1
  have hs (c : F) : σ c = c := by
    have hh := hσ c v
    rw [hvfix, hfix] at hh
    exact (smul_left_injective F hv) hh.symm
  simpa only [hs] using hσ

/-- In the hypothetical rank-three alternative every actor is field-linear. -/
theorem near_offender_field_linear_of_no_rank_two
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hnear : fixedCodim (normalizerRepresentation action) A ≤ rank A + 1)
    (hno : ∀ t ∈ A, t ≠ 1 → operatorFixedCodim t.val.val ≠ 2) :
    ∀ t ∈ A, ∀ (c : F) (M : V), t.val.val (c • M) = c • t.val.val M := by
  obtain ⟨hr, hc, hu⟩ := near_offender_uniform_of_no_rank_two A hA hnear hno
  obtain ⟨u, huA, hu1, r, _, _, hur⟩ :=
    exists_inner_involution_of_rank_ge_three A hA hr.ge
  let W := fixedSpace (normalizerRepresentation action) A
  have he : W = fixedSpace (normalizerRepresentation action) (zpowers u) := by
    apply fixedSpace_eq_of_fixedCodim_eq _ (zpowers_le.mpr huA)
    rw [fixedCodim_zpowers_eq_displacement_rank, hc]
    exact (hu u huA hu1).symm
  have hW : ∀ (c : F) (v : V), v ∈ W → c • v ∈ W := by
    intro c v hv
    have hrv : matrixAction r v = v := by
      have hh := hv ⟨u, huA⟩
      change u.val.val v = v at hh
      rw [hur] at hh
      exact hh
    rw [he, mem_fixedSpace_zpowers_iff]
    change u.val.val (c • v) = c • v
    rw [hur]
    change matrixAction r (c • v) = c • v
    rw [map_smul, hrv]
  have hn : W ≠ ⊥ := by
    intro hh
    have hd := fixedCodim_add_finrank (normalizerRepresentation action) A
    change fixedCodim (normalizerRepresentation action) A + finrank (ZMod 2) W = _ at hd
    rw [hc, finrank_binary, hh, finrank_bot] at hd
    omega
  obtain ⟨v, hvW, hv⟩ := W.ne_bot_iff.mp hn
  intro t ht
  exact normalizer_field_linear_of_fixed_scalar_orbit
    (LinearMap.GeneralLinearGroup.toLinearEquiv t.val) (normalizer_linearEquiv_mem t)
    v hv (fun c => hW c v hvW ⟨t, ht⟩)

/-- Field-linear actors retain their original underlying operators in a
faithful homomorphism to the field general linear group. -/
theorem exists_field_actor_hom (A : Subgroup (linearNormalizer action))
    (hl : ∀ t ∈ A, ∀ (c : F) (M : V), t.val.val (c • M) = c • t.val.val M) :
    ∃ f : A →* (V ≃ₗ[F] V), Function.Injective f ∧
      ∀ t v, f t v = t.val.val.val v := by
  let e (t : A) : V ≃ₗ[ZMod 2] V := LinearMap.GeneralLinearGroup.toLinearEquiv t.val.val
  let l (t : A) : V →ₗ[F] V :=
    { toFun := e t
      map_add' := (e t).map_add
      map_smul' := hl t t.property }
  let f : A →* (V ≃ₗ[F] V) :=
    { toFun t := LinearEquiv.ofBijective (l t) (e t).bijective
      map_one' := by apply LinearEquiv.ext; intro v; rfl
      map_mul' := by intros; apply LinearEquiv.ext; intro v; rfl }
  refine ⟨f, ?_, fun _ _ => rfl⟩
  intro t u h
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  exact LinearEquiv.congr_fun h v

/-- Every inner involution is conjugate to a pair of either identities or
one prescribed nonidentity root involution. -/
theorem exists_standard_inner_conjugate
    (u : Matrix.SpecialLinearGroup (Fin 2) F) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (r : G) (hr2 : r * r = 1) (hr1 : r ≠ 1) :
    ∃ s c : G, (s.1 = 1 ∨ s.1 = u) ∧ (s.2 = 1 ∨ s.2 = u) ∧ s ≠ 1 ∧
      c * s * c⁻¹ = r := by
  have hf (a : Matrix.SpecialLinearGroup (Fin 2) F) (ha : a * a = 1) :
      ∃ b c : Matrix.SpecialLinearGroup (Fin 2) F,
        (b = 1 ∨ b = u) ∧ c * b * c⁻¹ = a := by
    by_cases h1 : a = 1
    · exact ⟨1, 1, Or.inl rfl, by simp [h1]⟩
    let e := Theory.PSL2.sl2QuotientEquiv F
    have haord : orderOf a = 2 := (orderOf_eq_prime_iff (p := 2)).mpr
      ⟨by rw [pow_two, ha], h1⟩
    have huord : orderOf u = 2 := (orderOf_eq_prime_iff (p := 2)).mpr
      ⟨by rw [pow_two, hu2], hu1⟩
    have hp := Theory.PSL2.involutions_isConj (e u) (e a)
      ((e.orderOf_eq u).trans huord) ((e.orderOf_eq a).trans haord)
    have hc : IsConj u a := by
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
        using e.symm.toMonoidHom.map_isConj hp
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    exact ⟨u, c, Or.inr rfl, hc⟩
  obtain ⟨a, c, ha, hc⟩ := hf r.1 (congrArg Prod.fst hr2)
  obtain ⟨b, d, hb, hd⟩ := hf r.2 (congrArg Prod.snd hr2)
  refine ⟨(a,b), (c,d), ha, hb, ?_, Prod.ext hc hd⟩
  intro hh
  have he : (c,d) * (a,b) * (c,d)⁻¹ = r := Prod.ext hc hd
  rw [hh, mul_one, mul_inv_cancel] at he
  exact hr1 he.symm

end ClassicalOrthogonal.FourPlusMatrix.Binary
