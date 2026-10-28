module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsRee
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsReeSpectrum

/-!
# Short-root exclusion in the original Ree cubic actor

The order-thirteen calculation gives displacement at least twelve in every
large exceptional factor. The actual tensor period and Schur-field descent
multiply this bound by 2m+1. Transport through the proved trivial center
retains the original faithful source action. Hence the saturated actor,
whose involutions all have displacement 10(2m+1), contains only long-root
involutions in the genuine Ree model.

This discharges the representation part of GM04 Lemma 8.8. The contradiction
from its relatively normal elementary subgroup remains a group-geometric
step; no complete source exclusion is asserted.
Source: GM04 Lemmas 2.3,8.8, internal pp.6,57; Aschbacher--Smith K.3, p.457.
-/

public noncomputable section
open Module Representation Subgroup Theory.AlgebraicGroup
open Representation.FrobeniusTensor Representation.BinaryOffender
open Representation.TensorInvolutionDisplacement
open ReeF4 ReeF4.FixedSpaceEstimate ReeF4.BinaryDegree.ExceptionalTensor
namespace CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

private theorem short_tensor_bound {m : ℕ} (hm : 1 ≤ m)
    {W : Type v} [AddCommGroup W] [Module F W]
    (σ : Representation F (Model m) W) (hσ : Function.Injective σ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (hB : ∀ i, (B i).IsExceptionalBasic)
    (e : Representation.Equiv σ
      (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ)
    {s : ℕ} (hs : 0 < s) (hsn : s ∣ 2 * m + 1)
    (hshift : ∀ i, finrank F (B (i + 2 * (s : ZMod (2 * m + 1)))).Space =
      finrank F (B i).Space)
    (t : Model m) (ht : EvenInvolutionGeometry.IsShortRootInvolution t) :
    12 * (2 * m + 1) ≤ s * finrank F
      (W ⧸ invariants (σ.comp (Subgroup.zpowers t).subtype)) := by
  let τ := (exceptionalTensor
    (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ
  have hmap : (invariants (σ.comp (Subgroup.zpowers t).subtype)).map
      e.toLinearEquiv.toLinearMap = invariants (τ.comp (Subgroup.zpowers t).subtype) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩ g
      have hi := Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap g.val v
      change e (σ g.val v) = τ g.val (e v) at hi
      change τ g.val (e v) = e v
      have hv' : σ g.val v = v := hv g
      rw [← hi, hv']
    · intro hw
      refine ⟨e.toLinearEquiv.symm w, ?_, e.toLinearEquiv.apply_symm_apply w⟩
      intro g
      apply e.toLinearEquiv.injective
      have hi := Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap g.val
        (e.toLinearEquiv.symm w)
      change e (σ g.val (e.toLinearEquiv.symm w)) = τ g.val (e (e.toLinearEquiv.symm w)) at hi
      change e (σ g.val (e.toLinearEquiv.symm w)) = e (e.toLinearEquiv.symm w)
      rw [hi]
      have hew : e (e.toLinearEquiv.symm w) = w := e.toLinearEquiv.apply_symm_apply w
      rw [hew]
      exact hw g
  have he := (Submodule.Quotient.equiv _ _ e.toLinearEquiv hmap).finrank_eq
  rw [he]
  obtain ⟨i, hi⟩ := Classification.exists_nontrivial_factor_of_faithful σ hσ _ B e

  let ι := Classification.splitEmbedding (Classification.coefficientHom F m)
  let V : ℕ → FDRep F (Model m) := fun j => exceptionalFactor ι B (j : ZMod (2 * m + 1))
  have ht2 : t ^ 2 = 1 := by
    simpa only [EvenInvolutionGeometry.orderOf_of_isShortRootInvolution ht] using
      pow_orderOf_eq_one t
  have hcount := periodic_large_count_ge m s 26 hs hsn
    (fun j => finrank F (B j).Space) ⟨i, basicFactorMinimum_charTwo (B i) (hB i) hi⟩ hshift
  have hb := tensorPrefix_displacement_ge_count V t ht2 26 12 (by decide)
    (fun j => (B (j : ZMod (2 * m + 1))).finrank_pos)
    (fun j hj => by
      rw [operatorFixedCodim_eq_cyclicFixedCodim]
      exact ReeSpectrum.basic_short_involution_bound hm
        (Classification.coefficientHom F m) (B (j : ZMod (2 * m + 1)))
        (hB _) hj _ t ht) (2 * m + 1)
  rw [operatorFixedCodim_eq_cyclicFixedCodim] at hb
  have hn : s * ((2 * m + 1) / s) = 2 * m + 1 := Nat.mul_div_cancel' hsn
  have hbound := Nat.mul_le_mul_left s ((Nat.mul_le_mul_left 12 hcount).trans hb)
  rw [mul_left_comm s 12, hn] at hbound
  convert hbound using 1
  rfl

theorem ree_model_short_involution_bound {m : ℕ} (hm : 1 ≤ m)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Model m) V) [IsIrreducible ρ]
    (hf : Function.Injective ρ) (t : Model m)
    (ht : EvenInvolutionGeometry.IsShortRootInvolution t) :
    12 * (2 * m + 1) ≤ fixedCodim ρ (zpowers t) := by
  let F := Closure ρ
  let σ := absoluteRep ρ
  have hσ : Function.Injective σ := absoluteRep_injective ρ hf
  have hU := Classification.Steinberg.Geometry.carrier_isUniversalVersion_of_semisimple_centers
    (F := F) (fun _ _ hH _ hT =>
      SemisimpleCenterContainment.center_le_maximalTorus_of_semisimple hH hT)
  have hi (B : ZMod (2 * m + 1) → AlgebraicFactor F) (hB : ∀ i, (B i).IsExceptionalBasic) :=
    Classification.Steinberg.FiniteRootAction.exceptionalTensor_irreducible m B hU hB
      (Classification.coefficientHom F m)
  have hu := Classification.Steinberg.FiniteRootAction.exceptionalTensor_distinction m hU
  obtain ⟨B, hB, ⟨e⟩⟩ := Classification.Steinberg.FiniteRootAction.exists_tensor_of_class_bound
    m hU (Classification.coefficientHom F m) hu
    (Classification.Steinberg.Geometry.OddClasses.model_odd_class_bound m) σ
  obtain ⟨_, hperiod, hshift⟩ := Classification.factorization_consequences σ hσ
    (Classification.splitEmbedding (Classification.coefficientHom F m)) hi hu B hB e
    (Classification.Steinberg.SourceHighestWeight.character_shift
      (Classification.coefficientHom F m) B hB)
  apply binary_fixedCodim_ge_of_period_estimate ρ (zpowers t) hperiod
  intro s hs hsn hc
  exact short_tensor_bound hm σ hσ B hB e hs hsn (hshift s hc) t ht

variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [FiniteDimensional (ZMod 2) V] in
theorem ree_source_model_equiv (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e₀ : L ⧸ center L ≃* Model m) :
    ∃ e : L ≃* Model m, e.toMonoidHom = e₀.toMonoidHom.comp (QuotientGroup.mk' (center L)) := by
  let := h.quasisimple
  let := h.irreducible
  have hz := Triality.InnerDisplacement.center_eq_bot_of_twoGroup (ρ.comp L.subtype)
    (h.faithful.comp Subtype.val_injective)
    (ReeF4.CentralCovers.OddPrimary.center_isPGroup_of_quotient_equiv m hm e₀)
  let e : L ≃* Model m :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e₀
  refine ⟨e, ?_⟩
  apply MonoidHom.ext
  intro x
  apply congrArg e₀
  change ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm x =
    QuotientGroup.mk' (center L) x
  apply ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).injective
  simp

theorem ree_source_short_involution_bound (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e₀ : L ⧸ center L ≃* Model m)
    (t : L)
    (ht : EvenInvolutionGeometry.IsShortRootInvolution
      (e₀ (QuotientGroup.mk' (center L) t))) :
    12 * (2 * m + 1) ≤ fixedCodim ρ (zpowers (t : G)) := by
  obtain ⟨e, he⟩ := ree_source_model_equiv h hm e₀
  have he' : e t = e₀ (QuotientGroup.mk' (center L) t) := DFunLike.congr_fun he t
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff _ e.symm.surjective _).mpr h.irreducible
  have hb := ree_model_short_involution_bound hm σ
    (h.faithful.comp (Subtype.val_injective.comp e.symm.injective)) (e t) (he'.symm ▸ ht)
  have heval : e.symm.toMonoidHom (e t) = t := e.symm_apply_apply t
  change 12 * (2 * m + 1) ≤ Module.finrank (ZMod 2)
    (V ⧸ invariants (σ.comp (zpowers (e t)).subtype)) at hb
  change 12 * (2 * m + 1) ≤ Module.finrank (ZMod 2)
    (V ⧸ invariants (((ρ.comp L.subtype).comp e.symm.toMonoidHom).comp
      (zpowers (e t)).subtype)) at hb
  rw [invariants_comp_zpowers, heval, invariants_comp_zpowers ρ L.subtype t] at hb
  exact hb

theorem ree_small_actor_long_root_pure (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e₀ : L ⧸ center L ≃* Model m)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    ∀ t : L, (t : G) ∈ A → t ≠ 1 →
      EvenInvolutionGeometry.IsLongRootInvolution (e₀ (QuotientGroup.mk' (center L) t)) := by
  let := hA.2
  obtain ⟨e, he⟩ := ree_source_model_equiv h hm e₀
  intro t ht ht1
  have he' : e t = e₀ (QuotientGroup.mk' (center L) t) := DFunLike.congr_fun he t
  have ht2 : t ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (t : G) ht)
  have hne : e t ≠ 1 := fun hh => ht1 (e.injective (hh.trans e.map_one.symm))
  have hsq : e t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  rcases BasicInvolutions.InversionCoverage.root_coverage_of_unipotent
    (BasicInvolutions.InversionCoverage.unipotentRootCoverage m hm) (e t) hne hsq with hl | hs
  · exact he' ▸ hl
  · have hb := ree_source_short_involution_bound h hm e₀ t (he' ▸ hs)
    have ha := ree_small_actor_saturated h hm e₀ A hA hsmall
    have htG : (t : G) ≠ 1 := fun hh => ht1 (Subtype.ext hh)
    have hc := (ha.2.2.2.2 t ht htG).1
    omega

end CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
