module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsTrialityTensor
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate
/-!
# Original-action displacement and short-root exclusion for triality

The tensor estimate descends through the actual Schur field and central-cover
isomorphism. It bounds every inner involution by more than 5r and every
short-root involution by at least 11r, retaining the original quotient map.
Source: GM04 Lemma 8.6; Aschbacher--Smith K.3, printed p.457.
-/
public noncomputable section
open ReeF4.FixedSpaceEstimate
open scoped MonoidAlgebra
open Subgroup Theory.GroupTheory
open Representation Representation.FrobeniusTensor Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open Triality.RestrictedWeights Triality.RestrictedWeights.Concrete
open Triality.RestrictedWeights.SteinbergTensors
open Triality.Standard Triality.SimplyConnected
namespace CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
universe u v
theorem triality_model_inner_displacement {n : ℕ} (hn : 0 < n)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (BinaryCarrier n hn) V)
    [IsIrreducible ρ] (hf : Function.Injective ρ) (t : BinaryCarrier n hn) (ht : orderOf t=2) :
    5*n < fixedCodim ρ (zpowers t) ∧
      (EvenInvolutionGeometry.IsShortRootInvolution n hn t →
        11*n ≤ fixedCodim ρ (zpowers t)) := by
  let k := Closure ρ
  let hu := source_universal k
  let σ := absoluteRep ρ
  have hiσ : IsIrreducible (FDRep.of σ).ρ := absoluteRepIrreducible ρ
  have hfσ : Function.Injective (FDRep.of σ).ρ := absoluteRep_injective ρ hf
  obtain ⟨a, ⟨e⟩, _⟩ := native_tensor_exhaustive k hu n hn (FDRep.of σ) hiσ
  let R := tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
    (nativePointHom k n hn) (extendWeights hn a) n
  have hR : Function.Injective R.ρ := by
    intro x y hxy
    apply hfσ
    apply e.conj.injective
    simpa only [Representation.Equiv.conj_apply_self] using hxy
  have hchar (r : ℕ) :
      (∀ g, Representation.character R.ρ g ^ (2 ^ r) = Representation.character R.ρ g) ↔
        Module.finrank (ZMod 2) (SchurField ρ) ∣ r := by
    have he : Representation.character R.ρ = Representation.character σ :=
      (Representation.char_iso e).symm
    rw [he]
    exact character_pow_iff ρ r
  let s := Module.finrank (ZMod 2) (SchurField ρ)
  have hs : 0 < s := schurField_finrank_pos ρ
  have hsn : s ∣ 3 * n := (hchar _).mp
    ((native_tensor_character_period k hu n hn a _).mpr (extendWeights_period_three hn a))
  have hp : Function.Periodic (extendWeights hn a) s :=
    (native_tensor_character_period k hu n hn a _).mp ((hchar _).mpr (dvd_refl s))
  obtain ⟨i, hi⟩ := native_tensor_nonzero_weight k hu n hn (extendWeights hn a)
    (EvenInvolutionGeometry.longRoot n hn 1)
    (EvenInvolutionGeometry.longRoot_orderOf n hn one_ne_zero) hR
  have hinner := native_tensor_involution_displacement k hu n hn (extendWeights hn a)
    s hs hsn (extendWeights_wrap hn a) hp ⟨i,hi⟩ t ht
  have hshort (hts : EvenInvolutionGeometry.IsShortRootInvolution n hn t) :=
    triality_tensor_short_bound k hu n hn (extendWeights hn a)
      s hs hsn (extendWeights_wrap hn a) hp ⟨i,hi⟩ t hts
  have he := operatorFixedCodim_eq_of_equiv (σ t) (R.ρ t) e.toLinearEquiv
    (fun v => LinearMap.congr_fun (e.isIntertwining' t) v)
  have hd : fixedCodim ρ (zpowers t) = s * operatorFixedCodim (σ t) := by
    change Module.finrank (ZMod 2) (V ⧸ invariants (ρ.comp (zpowers t).subtype)) = _
    rw [ReeF4.FixedSpaceEstimate.binary_fixedCodim_eq_schur_mul]
    rw [ReeF4.FixedSpaceEstimate.BasicInvolutions.cyclic_fixedCodim_eq_rank]
    rfl
  rw [hd,he]
  exact ⟨hinner,hshort⟩

variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [FiniteDimensional (ZMod 2) V] in
theorem triality_source_model_equiv (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 0<n)
    (hm : IsTrialityGroupAt (2^n) (L ⧸ center L)) :
    ∃ e : L ≃* BinaryCarrier n hn,
      ∃ e₀ : (L ⧸ center L) ≃* BinaryCarrier n hn,
        e.toMonoidHom = e₀.toMonoidHom.comp (QuotientGroup.mk' (center L)) := by
  let := h.quasisimple
  let := h.irreducible
  have hz := Triality.InnerDisplacement.center_eq_bot_of_twoGroup (ρ.comp L.subtype)
    (h.faithful.comp Subtype.val_injective)
    (Triality.InnerDisplacement.PrimeToTwoCovers.center_isTwoGroup n hn hm)
  obtain ⟨e₀⟩ := (isTrialityGroupAt_binary_iff _ n hn).mp hm
  let e : L ≃* BinaryCarrier n hn :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e₀
  refine ⟨e,e₀,?_⟩
  apply MonoidHom.ext
  intro x
  apply congrArg e₀
  change ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm x =
    QuotientGroup.mk' (center L) x
  apply ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).injective
  simp

omit [Finite G] in
theorem triality_source_inner_displacement (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 0<n) (e : L ≃* BinaryCarrier n hn) (t : L) (ht : orderOf t=2) :
    5*n < fixedCodim ρ (zpowers (t : G)) ∧
      (EvenInvolutionGeometry.IsShortRootInvolution n hn (e t) →
        11*n ≤ fixedCodim ρ (zpowers (t : G))) := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff _ e.symm.surjective _).mpr h.irreducible
  have hb := triality_model_inner_displacement hn σ
    (h.faithful.comp (Subtype.val_injective.comp e.symm.injective)) (e t)
    ((e.orderOf_eq t).trans ht)
  have heval : e.symm.toMonoidHom (e t) = t := e.symm_apply_apply t
  have hd : fixedCodim σ (zpowers (e t)) = fixedCodim ρ (zpowers (t : G)) := by
    change Module.finrank (ZMod 2)
      (V ⧸ invariants (((ρ.comp L.subtype).comp e.symm.toMonoidHom).comp
        (zpowers (e t)).subtype)) = _
    rw [invariants_comp_zpowers, heval, invariants_comp_zpowers ρ L.subtype t]
    rfl
  rwa [hd] at hb

/-- No short-root involution can belong to a source actor of ratio at most two. -/
theorem triality_small_actor_no_short (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 0<n) (hm : IsTrialityGroupAt (2^n) (L ⧸ center L))
    (e : L ≃* BinaryCarrier n hn)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    ∀ t : L, (t : G) ∈ A → ¬ EvenInvolutionGeometry.IsShortRootInvolution n hn (e t) := by
  intro t ht hs
  have ho : orderOf t=2 := (e.orderOf_eq t).symm.trans hs.orderOf_eq_two
  have hb := (triality_source_inner_displacement h hn e t ho).2 hs
  have hr := triality_source_actor_rank h hn hm A hA
  have hmono := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ht))
  have hdt := fixedCodim_add_finrank ρ (zpowers (t : G))
  have hdA := fixedCodim_add_finrank ρ A
  omega
end CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
