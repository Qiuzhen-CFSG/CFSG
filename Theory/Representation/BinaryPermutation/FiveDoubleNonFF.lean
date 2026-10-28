module
public import Theory.Representation.BinaryPermutation.FiveTensorNormalizer
public import Theory.Representation.BinaryPermutation.FiveTensorLowRank
public import Theory.Representation.BinaryOffender.Replacement
public import Theory.Representation.BinaryOffender.NormalizerNonFF
public import Theory.Representation.BinaryOffender.NormalizerOffenderDimension
public import Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank

/-!
# The doubled binary A₅ module is not an FF module for its full normalizer

The tensor model identifies the full linear normalizer of two natural A₅
copies with a subgroup of S₅ × S₃. A displacement-rank calculation rules out
quadratic offenders in either projection case; minimal-best-offender
replacement then rules out all offenders. The marked-normal-range theorem
transports this result to the literal doubled module.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Appendix B.5 and the binary tensor calculation in Chapter 13.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender TensorProduct
namespace BinaryPermutation.FiveDoubleNonFF
abbrev Actor := Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)
abbrev Space := core (Fin 5) ⊗[ZMod 2] core (Fin 3)
abbrev tensor := ThreeTensor.action (coreRepresentation (Fin 5))

private theorem core_faithful : Function.Injective (coreRepresentation (Fin 5)) := by
  intro g h he
  have hh : tensor (g,1) = tensor (h,1) := by
    apply LinearMap.ext
    intro v
    apply ThreeTensor.pairEquiv.injective
    rw [ThreeTensor.pairEquiv_equivariant,ThreeTensor.pairEquiv_equivariant]
    change (coreRepresentation (Fin 5) g (ThreeTensor.pairEquiv v).1,
      coreRepresentation (Fin 5) g (ThreeTensor.pairEquiv v).2) =
      (coreRepresentation (Fin 5) h (ThreeTensor.pairEquiv v).1,
      coreRepresentation (Fin 5) h (ThreeTensor.pairEquiv v).2)
    rw [he]
  exact congrArg Prod.fst (FiveTensorNormalizer.tensor_faithful hh)

/-- The full S₅ × S₃ tensor action admits no quadratic offender. -/
theorem not_quadratic_offender (A : Subgroup Actor) (hq : IsQuadratic tensor A) :
    ¬ IsOffender tensor A := by
  intro hA
  let : IsElementaryAbelian 2 A := hA.1.2
  by_cases hout : ∃ a ∈ A, a.2 ≠ 1
  · have hb := ThreeTensor.outer_bound (coreRepresentation (Fin 5)) core_faithful
      (by rw [finrank_core]; decide) A hA.1 hq hout
    change 2 * rank A < fixedCodim tensor A at hb
    have hl := hA.2
    omega
  push Not at hout
  let f : A →* Equiv.Perm (Fin 5) := (MonoidHom.fst _ _).comp A.subtype
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact Prod.ext h ((hout a a.property).trans (hout b b.property).symm)
  have hr : rank A ≤ 2 := by
    change Nat.log 2 (Nat.card A) ≤ 2
    rw [IsElementaryAbelian.log_card_eq_primeRank (p := 2) A]
    exact (primeRank_le_of_injective 2 f hf).trans
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
  have hsmall (a : Actor) (ha : a ∈ A) :
      Module.finrank (ZMod 2) (LinearMap.range (tensor a - LinearMap.id)) ≤ rank A := by
    rw [← fixedCodim_zpowers_eq_displacement_rank]
    exact hA.fixedCodim_zpowers_le_rank tensor ha
  have hs : Function.Injective ((Equiv.Perm.sign : Equiv.Perm (Fin 5) →* ℤˣ).comp f) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply Subtype.ext
    by_contra hn
    obtain ⟨⟨i,j,hij,he⟩,_⟩ := FiveTensorLowRank.inspection a hn
      ((hsmall a a.property).trans hr)
    have hsign : Equiv.Perm.sign a.val.1 = 1 := ha
    rw [he, Equiv.Perm.sign_swap hij] at hsign
    exact (by decide : (-1 : ℤˣ) ≠ 1) hsign
  have hc : Nat.card A ≤ 2 := by
    have hc := Nat.card_le_card_of_injective _ hs
    exact hc.trans_eq (by simp [Nat.card_eq_fintype_card] : Nat.card ℤˣ = 2)
  have hr1 : rank A ≤ 1 := by
    change Nat.log 2 (Nat.card A) ≤ 1
    exact (Nat.log_mono_right hc).trans_eq (by decide)
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1.1
  have hh := (FiveTensorLowRank.inspection a ha1 ((hsmall a ha).trans hr)).2
  have hh' := hsmall a ha
  change Module.finrank (ZMod 2) (LinearMap.range (tensor a - LinearMap.id)) = 2 at hh
  have htwo : 2 ≤ rank A := by
    calc
      2 = Module.finrank (ZMod 2) (LinearMap.range (tensor a - LinearMap.id)) := hh.symm
      _ ≤ rank A := hh'
  omega

/-- Replacement reduces every proposed offender to the excluded quadratic case. -/
theorem tensor_not_isFFModule : ¬ IsFFModule tensor := by
  rintro ⟨A,hA⟩
  obtain ⟨B,_,hB,hq⟩ := hA.exists_quadratic_minimalBestOffender tensor
  exact not_quadratic_offender B hq.1 (hB.1.isOffender tensor)

abbrev double := Representation.prod (alternatingCoreRepresentation (Fin 5))
  (alternatingCoreRepresentation (Fin 5))
abbrev PairSpace := core (Fin 5) × core (Fin 5)

private theorem double_faithful : Function.Injective double := by
  intro g h he
  apply Subtype.ext
  apply core_faithful
  apply LinearMap.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun he (v,0))

private theorem normalizer_coordinates (a : linearNormalizer double) :
    ∃ p : Actor, ∀ v : Space,
      ThreeTensor.pairEquiv.symm (normalizerRepresentation double a (ThreeTensor.pairEquiv v)) =
        tensor p v := by
  let e := MonoidHom.ofInjective (show Function.Injective double.asGroupHom from
    fun x y h => double_faithful (congrArg Units.val h))
  let a' : normalizer (actionImage double : Set (Module.End (ZMod 2) PairSpace)ˣ) :=
    ⟨a.val,a.property⟩
  let φ := e.trans (((actionImage double).normalizerMonoidHom a').trans e.symm)
  let A : PairSpace ≃ₗ[ZMod 2] PairSpace :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) PairSpace a.val
  let F : Space ≃ₗ[ZMod 2] Space :=
    ThreeTensor.pairEquiv.trans (A.trans ThreeTensor.pairEquiv.symm)
  have hconj (g : alternatingGroup (Fin 5)) :
      double.asGroupHom (φ g) = a.val * double.asGroupHom g * a.val⁻¹ := by
    exact congrArg Subtype.val
      (e.apply_symm_apply ((actionImage double).normalizerMonoidHom a' (e g)))
  have hF (v : Space) : ThreeTensor.pairEquiv (F v) = A (ThreeTensor.pairEquiv v) :=
    ThreeTensor.pairEquiv.apply_symm_apply _
  apply FiveTensorNormalizer.tensor_normalizer F φ
  intro g v
  apply ThreeTensor.pairEquiv.injective
  rw [hF]
  rw [ThreeTensor.pairEquiv_equivariant,ThreeTensor.pairEquiv_equivariant]
  have hh := congrArg (fun u : (Module.End (ZMod 2) PairSpace)ˣ =>
    u.val (A (ThreeTensor.pairEquiv v))) (hconj g)
  change A (double g (ThreeTensor.pairEquiv v)) =
    double (φ g) (ThreeTensor.pairEquiv (F v))
  rw [hF]
  change A (double g (ThreeTensor.pairEquiv v)) =
    (double.asGroupHom (φ g)).val (A (ThreeTensor.pairEquiv v))
  rw [hconj]
  change A (double g (ThreeTensor.pairEquiv v)) =
    A (double g (A.symm (A (ThreeTensor.pairEquiv v))))
  rw [A.symm_apply_apply]

private def normalizerEmbedding : linearNormalizer double →* Actor := by
  classical
  choose p hp using normalizer_coordinates
  refine { toFun := p, map_one' := ?_, map_mul' := ?_ }
  · apply FiveTensorNormalizer.tensor_coordinates_unique
    intro v
    rw [← hp]
    simp only [map_one,Module.End.one_apply,LinearEquiv.symm_apply_apply]
  · intro a b
    apply FiveTensorNormalizer.tensor_coordinates_unique
    intro v
    change tensor (p (a*b)) v = tensor (p a * p b) v
    rw [map_mul,Module.End.mul_apply,← hp,← hp,← hp]
    simp only [map_mul,Module.End.mul_apply,LinearEquiv.apply_symm_apply]

private theorem normalizerEmbedding_action (a : linearNormalizer double) (v : Space) :
    ThreeTensor.pairEquiv.symm (normalizerRepresentation double a (ThreeTensor.pairEquiv v)) =
      tensor (normalizerEmbedding a) v :=
  Classical.choose_spec (normalizer_coordinates a) v

/-- The full linear normalizer includes the multiplicity-space automorphisms;
its tautological action still admits no offender. -/
theorem double_normalizer_not_isFFModule :
    ¬ IsFFModule (normalizerRepresentation double) := by
  have hi : Function.Injective normalizerEmbedding := by
    intro a b he
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := (ThreeTensor.pairEquiv (V := core (Fin 5))).surjective w
    apply (ThreeTensor.pairEquiv (V := core (Fin 5))).symm.injective
    change ThreeTensor.pairEquiv.symm
      (normalizerRepresentation double a (ThreeTensor.pairEquiv v)) =
      ThreeTensor.pairEquiv.symm (normalizerRepresentation double b (ThreeTensor.pairEquiv v))
    rw [normalizerEmbedding_action,normalizerEmbedding_action,he]
  intro hf
  apply tensor_not_isFFModule
  apply hf.map_equivariant (normalizerRepresentation double) tensor normalizerEmbedding hi
    ThreeTensor.pairEquiv.symm
  intro a w
  obtain ⟨v,rfl⟩ := (ThreeTensor.pairEquiv (V := core (Fin 5))).surjective w
  simpa only [LinearEquiv.symm_apply_apply] using normalizerEmbedding_action a v

/-- Application to a faithful ambient action with a normal marked doubled A₅
subgroup, preserving the original surjective marking and coordinates. -/
theorem not_isFFModule_of_marked_double
    {H K U : Type*} [Group H] [Group K] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : K →* H) [i.range.Normal] (f : K →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) (b : Representation.Equiv (ρ.comp i) (double.comp f)) :
    ¬ IsFFModule ρ :=
  not_isFFModule_of_marked_normal_range ρ hρ i double f hf b double_normalizer_not_isFFModule

end BinaryPermutation.FiveDoubleNonFF
