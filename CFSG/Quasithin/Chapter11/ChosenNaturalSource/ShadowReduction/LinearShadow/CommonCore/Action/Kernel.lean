module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Definitions
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The literal faithful action in 11.3.7(1)

The two-core of H centralizes the H-span of its Sylow omega-center. Therefore
O₂(K), for K = O²(H), acts trivially. Simplicity of K/O₂(K) makes the induced
action either faithful or trivial. Since H = KT and T centralizes the seed,
the movement assumption [Z,H] ≠ 1 excludes the trivial action.

The exported star group is the literal H/C_H(V_H). Its action is faithful,
and the isomorphism K/O₂(K) ≃ K* commutes with the actual projections. The
source applications use only the rank-one quotient recognition supplied by
11.3.5--6; they do not assume an action-kernel equality. The natural-summand,
Cartan, fixed-space and transvection arguments in 11.3.7 remain separate.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.7(1), printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] (T : Sylow 2 G) (H : Subgroup G)

theorem omegaCenter_le_sylow : omegaCenter T ≤ (T : Subgroup G) :=
  (omegaOneAmbient_le _).trans (map_subtype_le _)

theorem omegaCenter_le_sylow_centralizer :
    omegaCenter T ≤ centralizer (T : Set G) := by
  rintro z hz t ht
  obtain ⟨w, hw, rfl⟩ := omegaOneAmbient_le _ hz
  exact congrArg Subtype.val (mem_center_iff.mp hw ⟨t, ht⟩)

theorem omegaClosure_eq_span : omegaClosure T H = conjugateSpanBy (omegaCenter T) H :=
  (conjugateSpanBy_eq_iSup_conj _ _).symm

theorem omegaCenter_le_closure : omegaCenter T ≤ omegaClosure T H := by
  rw [omegaClosure_eq_span]
  exact le_conjugateSpanBy _ _

theorem omegaClosure_normalized : H ≤ normalizer (omegaClosure T H : Set G) := by
  rw [omegaClosure_eq_span]
  exact le_normalizer_conjugateSpanBy _ _

theorem omegaClosure_le (hTH : (T : Subgroup G) ≤ H) : omegaClosure T H ≤ H := by
  rw [omegaClosure_eq_span]
  exact conjugateSpanBy_le ((omegaCenter_le_sylow T).trans hTH) H.le_normalizer

theorem outsideResidual_le : outsideResidual H ≤ H := map_subtype_le _

theorem outsideResidual_normalized : H ≤ normalizer (outsideResidual H : Set G) :=
  le_normalizer_embedded_pResidual 2 H

variable [Finite G]

theorem outsideResidual_sup_sylow (hTH : (T : Subgroup G) ≤ H) :
    outsideResidual H ⊔ (T : Subgroup G) = H := by
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  simpa only [outsideResidual, Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
    ← MonoidHom.range_eq_map, range_subtype] using he

omit [Finite G] in
theorem core_centralizes_omegaClosure (hTH : (T : Subgroup G) ≤ H) :
    H.pCoreIn 2 ≤ centralizer (omegaClosure T H : Set G) := by
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hc := pCoreIn_le_sylow H (T.subtype hTH)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using hc
  apply le_centralizer_iff.mpr
  rw [omegaClosure_eq_span]
  apply conjugateSpanBy_le ((omegaCenter_le_sylow_centralizer T).trans (centralizer_le hQT))
  exact (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))).trans
    (normalizer_le_normalizer_centralizer _)

omit [Finite G] in
theorem residual_core_centralizes_omegaClosure (hTH : (T : Subgroup G) ≤ H) :
    (outsideResidual H).pCoreIn 2 ≤ centralizer (omegaClosure T H : Set G) :=
  (pCoreIn_mono_of_normalizes (outsideResidual_le H) (outsideResidual_normalized H)).trans
    (core_centralizes_omegaClosure T H hTH)

omit [Finite G] in
def localAction : H →* MulAut (omegaClosure T H) :=
  (omegaClosure T H).normalizerMonoidHom.comp (inclusion (omegaClosure_normalized T H))

omit [Finite G] in
theorem localAction_apply (h : H) (v : omegaClosure T H) :
    (localAction T H h v : G) = (h : G) * (v : G) * (h : G)⁻¹ := rfl

omit [Finite G] in
theorem localAction_ker :
    (localAction T H).ker = (centralizer (omegaClosure T H : Set G)).subgroupOf H := by
  ext h
  rw [MonoidHom.mem_ker]
  constructor
  · intro he v hv
    have hf := congrArg (fun a : MulAut (omegaClosure T H) => (a ⟨v,hv⟩ : G)) he
    change (h : G) * v * (h : G)⁻¹ = v at hf
    exact (mul_inv_eq_iff_eq_mul.mp hf).symm
  · intro hc
    ext v
    change (h : G) * (v : G) * (h : G)⁻¹ = (v : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hc v v.property).symm

omit [Finite G] in
def residualAction : outsideResidual H →* MulAut (omegaClosure T H) :=
  (localAction T H).comp (inclusion (outsideResidual_le H))

omit [Finite G] in
theorem residualAction_ker :
    (residualAction T H).ker =
      (centralizer (omegaClosure T H : Set G)).subgroupOf (outsideResidual H) := by
  rw [residualAction, ← MonoidHom.comap_ker, localAction_ker]
  rfl

omit [Finite G] in
theorem residualAction_core_le_ker (hTH : (T : Subgroup G) ≤ H) :
    pCore 2 (outsideResidual H) ≤ (residualAction T H).ker := by
  rw [residualAction_ker]
  intro k hk
  exact residual_core_centralizes_omegaClosure T H hTH (mem_map_of_mem _ hk)

theorem residualAction_nontrivial (hTH : (T : Subgroup G) ≤ H)
    (hmove : ⁅omegaCenter T, H⁆ ≠ ⊥) : (residualAction T H).ker ≠ ⊤ := by
  intro he
  apply hmove
  apply commutator_eq_bot_iff_le_centralizer.mpr
  have hk : outsideResidual H ≤ centralizer (omegaClosure T H : Set G) := by
    intro k hk
    have hh : (⟨k,hk⟩ : outsideResidual H) ∈ (residualAction T H).ker := he ▸ mem_top _
    rw [residualAction_ker] at hh
    exact hh
  have hzK : omegaCenter T ≤ centralizer (outsideResidual H : Set G) :=
    (omegaCenter_le_closure T H).trans (le_centralizer_iff.mp hk)
  apply le_centralizer_iff.mpr
  rw [← outsideResidual_sup_sylow T H hTH]
  exact sup_le (le_centralizer_iff.mp hzK)
    (le_centralizer_iff.mp (omegaCenter_le_sylow_centralizer T))

theorem residualAction_ker_eq_core (hTH : (T : Subgroup G) ≤ H)
    (hmove : ⁅omegaCenter T, H⁆ ≠ ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))] :
    (residualAction T H).ker = pCore 2 (outsideResidual H) := by
  let C := (residualAction T H).ker
  let Q := pCore 2 (outsideResidual H)
  let q := QuotientGroup.mk' Q
  have hQC : Q ≤ C := residualAction_core_le_ker T H hTH
  have hn : (C.map q).Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective Q)
  rcases hn.eq_bot_or_eq_top with hz | ht
  · apply le_antisymm ?_ hQC
    have hc : C ≤ (C.map q).comap q := le_comap_map q C
    rw [hz, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hc
    exact hc
  · have hc := congrArg (comap q) ht
    rw [comap_map_eq, sup_eq_left.mpr (by simpa only [q, QuotientGroup.ker_mk'] using hQC),
      comap_top] at hc
    exact (residualAction_nontrivial T H hTH hmove hc).elim


omit [Finite G] in
instance localCentralizer_normal :
    ((centralizer (omegaClosure T H : Set G)).subgroupOf H).Normal := by
  rw [← localAction_ker]
  infer_instance

omit [Finite G] in
abbrev Star := H ⧸ (centralizer (omegaClosure T H : Set G)).subgroupOf H

omit [Finite G] in
def starProjection : H →* Star T H :=
  QuotientGroup.mk' ((centralizer (omegaClosure T H : Set G)).subgroupOf H)

omit [Finite G] in
def starAction : Star T H →* MulAut (omegaClosure T H) :=
  QuotientGroup.lift _ (localAction T H) (localAction_ker T H).ge

omit [Finite G] in
theorem starAction_injective : Function.Injective (starAction T H) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (localAction_ker T H).symm

omit [Finite G] in
theorem starAction_apply (h : H) (v : omegaClosure T H) :
    (starAction T H (starProjection T H h) v : G) =
      (h : G) * (v : G) * (h : G)⁻¹ := rfl

omit [Finite G] in
def residualStar : Subgroup (Star T H) :=
  ((outsideResidual H).subgroupOf H).map (starProjection T H)

omit [Finite G] in
def residualStarMap : outsideResidual H →* Star T H :=
  (starProjection T H).comp (inclusion (outsideResidual_le H))

omit [Finite G] in
theorem residualStarMap_ker : (residualStarMap T H).ker = (residualAction T H).ker := by
  rw [residualStarMap, ← MonoidHom.comap_ker]
  rw [starProjection, QuotientGroup.ker_mk']
  rw [residualAction_ker]
  rfl

omit [Finite G] in
theorem residualStarMap_range : (residualStarMap T H).range = residualStar T H := by
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨inclusion (outsideResidual_le H) k,k.property,rfl⟩
  · rintro ⟨h,hh,rfl⟩
    exact ⟨⟨h,hh⟩,rfl⟩

def residualQuotientAction (hTH : (T : Subgroup G) ≤ H) :
    (outsideResidual H ⧸ pCore 2 (outsideResidual H)) →* MulAut (omegaClosure T H) :=
  QuotientGroup.lift _ (residualAction T H) (residualAction_core_le_ker T H hTH)

omit [Finite G] in
theorem residualQuotientAction_apply (hTH : (T : Subgroup G) ≤ H)
    (k : outsideResidual H) (v : omegaClosure T H) :
    (residualQuotientAction T H hTH (QuotientGroup.mk' _ k) v : G) =
      (k : G) * (v : G) * (k : G)⁻¹ := rfl

theorem residualQuotientAction_injective (hTH : (T : Subgroup G) ≤ H)
    (hmove : ⁅omegaCenter T, H⁆ ≠ ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))] :
    Function.Injective (residualQuotientAction T H hTH) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr
    (residualAction_ker_eq_core T H hTH hmove).symm

def residualStarEquiv (hTH : (T : Subgroup G) ≤ H)
    (hmove : ⁅omegaCenter T, H⁆ ≠ ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))] :
    (outsideResidual H ⧸ pCore 2 (outsideResidual H)) ≃* residualStar T H :=
  ((QuotientGroup.quotientMulEquivOfEq
    ((residualStarMap_ker T H).trans (residualAction_ker_eq_core T H hTH hmove)).symm).trans
      (QuotientGroup.quotientKerEquivRange (residualStarMap T H))).trans
        (MulEquiv.subgroupCongr (residualStarMap_range T H))

theorem residualStarEquiv_apply (hTH : (T : Subgroup G) ≤ H)
    (hmove : ⁅omegaCenter T, H⁆ ≠ ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))]
    (k : outsideResidual H) :
    (residualStarEquiv T H hTH hmove (QuotientGroup.mk' _ k) : Star T H) =
      starProjection T H (inclusion (outsideResidual_le H) k) := rfl

theorem residual_centralizer_eq_core (hTH : (T : Subgroup G) ≤ H)
    (hmove : ⁅omegaCenter T, H⁆ ≠ ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))] :
    outsideResidual H ⊓ centralizer (omegaClosure T H : Set G) =
      (outsideResidual H).pCoreIn 2 := by
  have he := congrArg (map (outsideResidual H).subtype)
    (residualAction_ker_eq_core T H hTH hmove)
  rw [residualAction_ker, subgroupOf_map_subtype, inf_comm] at he
  exact he

variable {T H} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

theorem source_residualQuotient_simple
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H)) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hmodel
  let := hF
  let := hfin
  have hfour : 4 ≤ Nat.card F := by
    rw [hcard]
    exact (show 2 ^ 2 ≤ 2 ^ S.field.degree from Nat.pow_le_pow_right (by decide) S.nonbinary)
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  exact e.isSimpleGroup

theorem source_action_kernel (s : Hypothesis1131At D S U₁ H)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    outsideResidual H ⊓ centralizer (omegaClosure T H : Set G) =
      (outsideResidual H).pCoreIn 2 := by
  let := source_residualQuotient_simple hmodel
  exact residual_centralizer_eq_core T H s.outside.1.1.2 s.moves_omega_center

theorem source_faithful_quotient_action (s : Hypothesis1131At D S U₁ H)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    Function.Injective (residualQuotientAction T H s.outside.1.1.2) := by
  let := source_residualQuotient_simple hmodel
  exact residualQuotientAction_injective T H s.outside.1.1.2 s.moves_omega_center

theorem source_star_model (s : Hypothesis1131At D S U₁ H)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    ClassicalGroup.IsPSL (residualStar T H) 2 (2 ^ S.field.degree) := by
  let := source_residualQuotient_simple hmodel
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hmodel
  exact ⟨F,hF,hfin,hcard,⟨(residualStarEquiv T H s.outside.1.1.2
    s.moves_omega_center).symm.trans e⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
