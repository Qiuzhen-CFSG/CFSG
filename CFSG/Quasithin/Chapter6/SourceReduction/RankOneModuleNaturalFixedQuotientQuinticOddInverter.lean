module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOddImage
public import Theory.GroupTheory.CoreCentralNormalizerAction.PSL2Inverter

/-!
# Original odd linear-two inverters, with the full residual kernel

The whole quintic action has order five, so its kernel equals the original
residual's two-core. The supplied component Sylow gives an inverter in T∩K.
Its image in K/O₂(K)/Z is an involution; the original element inverts the
whole X modulo O₂(X), with no assertion that an involution lifts to one.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric

private theorem kernel_eq_twoCore_of_card_five {A B : Type*}
    [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f)
    (hB : Nat.card B = 5) (hA : Nat.card (A ⧸ pCore 2 A) = 5) :
    f.ker = pCore 2 A := by
  have hcard : Nat.card ((pCore 2 A).map f) = 1 :=
    ((pCore_isPGroup (p := 2) (G := A)).map f).card_eq_or_dvd.resolve_right (by
      intro hd
      have hh := hd.trans ((pCore 2 A).map f).card_subgroup_dvd_card
      rw [hB] at hh
      norm_num at hh)
  have hbot : (pCore 2 A).map f = ⊥ := eq_bot_of_card_eq ((pCore 2 A).map f) hcard
  have hle : pCore 2 A ≤ f.ker := (Subgroup.map_eq_bot_iff (pCore 2 A)).mp hbot
  have hi : f.ker.index = 5 := by
    rw [index_ker,f.range_eq_top_of_surjective hf,card_top,hB]
  have hj : (pCore 2 A).index = 5 := hA
  have hk := f.ker.card_mul_index
  have hc := (pCore 2 A).card_mul_index
  rw [hi] at hk
  rw [hj] at hc
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- On the original residual, triviality of the literal component action
is exactly membership in the whole original two-core. -/
theorem original_hermitian_quintic_odd_linear_action_kernel
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p d : ℕ) (hp : p.Prime) (ho : Odd p) (hd : d = 1 ∨ d = 2)
    (hc : ClassicalGroup.IsPSL (coreCentralQuotient K) 2 (p^d)) :
    ∀ x : normalizer (K : Set G), (x : G) ∈ quinticResidual T L →
      (normalizerCoreCentralAction K x = 1 ↔
        (x : G) ∈ (quinticResidual T L).pCoreIn 2) := by
  let X := quinticResidual T L
  let Y := coreCentralActorImage K X
  let N := normalizer (K : Set G)
  have hXN : X ≤ N := original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  let ex := (subgroupOfEquivOfLe hXN).symm
  let f : X →* Y := ((normalizerCoreCentralAction K).subgroupMap (X.subgroupOf N)).comp
    ex.toMonoidHom
  have hf : Function.Surjective f :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp ex.surjective
  have hker := kernel_eq_twoCore_of_card_five f hf
    (original_hermitian_quintic_odd_linear_image_card h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd hc)
    (original_hermitian_quintic_core_quotient h hout hm).2
  intro x hx
  let z : X := ⟨x,hx⟩
  calc
    normalizerCoreCentralAction K x = 1 ↔ f z = 1 :=
      ⟨fun hh => Subtype.ext hh,fun hh => congrArg Subtype.val hh⟩
    _ ↔ z ∈ pCore 2 X := by change z ∈ f.ker ↔ _; rw [hker]
    _ ↔ (x : G) ∈ X.pCoreIn 2 := (mem_map_iff_mem X.subtype_injective).symm

/-- The inverter lies in the original T∩K and inverts the whole original
residual modulo its full two-core. Its literal central quotient image has
order two; no order-two lift in the original group is assumed. -/
theorem original_hermitian_quintic_odd_linear_sylow_inverter
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p d : ℕ) (hp : p.Prime) (ho : Odd p) (hd : d = 1 ∨ d = 2)
    (hc : ClassicalGroup.IsPSL (coreCentralQuotient K) 2 (p^d)) :
    ∃ k : K, (k : G) ∈ T ∧ GorensteinWalter.IsInvolution (coreCentralProjection K k) ∧
      ∀ x ∈ quinticResidual T L,
        (k : G) * x * (k : G)⁻¹ * x ∈ (quinticResidual T L).pCoreIn 2 := by
  let X := quinticResidual T L
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) M₁ :=
    ⟨T.subtype hTM₁,map_subgroupOf_eq_of_le hTM₁⟩
  obtain ⟨U,hU⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hK.1 hK.2.subnormal
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    sylow_normalizes_quinticResidual (h.rankOneInput hout).sylow_normalizes
  have hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G) := by
    rw [hU]
    exact inf_le_left.trans hTX
  have hinner := original_hermitian_quintic_odd_linear_inner
    h hout hm hM₁ hCM₁ hK p d hp ho (by omega) hc
  have hfive := original_hermitian_quintic_odd_linear_image_card
    h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd hc
  have hkernel := original_hermitian_quintic_odd_linear_action_kernel
    h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd hc
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
  obtain ⟨k,hk,hki,hkinv⟩ := coreCentral_odd_quintic_sylow_inverter K X U hUX hinner hfive
    ⟨p,d,hp,ho,by omega,hF⟩ e
  have hkT : (k : G) ∈ T := by
    have hh := mem_map_of_mem K.subtype hk
    rw [hU] at hh
    exact hh.1
  refine ⟨k,hkT,hki,?_⟩
  intro x hx
  have hXN : X ≤ normalizer (K : Set G) :=
    original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  let z : normalizer (K : Set G) := ⟨x,hXN hx⟩
  let t : normalizer (K : Set G) := ⟨k,K.le_normalizer k.property⟩
  have hy : ((t*z*t⁻¹*z : normalizer (K : Set G)) : G) ∈ X :=
    X.mul_mem ((mem_normalizer_iff.mp (hTX hkT) x).mp hx) hx
  apply (hkernel (t*z*t⁻¹*z) hy).mp
  simp only [map_mul,map_inv]
  rw [hkinv z hx,inv_mul_cancel]

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
