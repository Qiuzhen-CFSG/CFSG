module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LocalSubgroups
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LocalExclusion
public import CFSG.Quasithin.Chapter13.Section02.CoveredNormalizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.NormalizerExclusion
public import Theory.GroupTheory.PResidual.KernelSupplement

/-!
# Distinct component automizers in the covered source case

Equality of the L₁ and L₁,+ automizers makes the residual of the actual
action kernel supplement L₁,+. Its T-invariance and the marked order-nine
quotient force it to contain L₀. Residual lifting then makes K normalize
L₀, contradicting the original13.3.9 exclusion from M. Component
normality, the marked directions, and the13.2.2(9) normalizer are proved
from the original setup. The earlier universal13.3.9 remains explicit.

Source: Aschbacher–Smith,13.7.5(7), printed p.938.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem covered_zero_normalizer
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    normalizer (zero L : Set G) ≤ M := by
  rcases NaturalModels.quotient_alternatives d with ⟨e, _⟩ | ⟨e, he⟩
  · obtain ⟨ec⟩ := hcover
    have hc := Nat.card_congr (centerCongr (e.symm.trans ec)).toEquiv
    rw [alternatingGroup.center_eq_bot (by simp), card_bot,
      Representation.Hexacode.even_center_card] at hc
    omega
  · obtain ⟨a⟩ := NaturalModels.covered_natural d e he
    rw [a.zero_normalizer_eq h, d.local_normalizer]

omit d in
private theorem star_centralizes_of_coreAction_eq_one
    (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    {Z : Subgroup G}
    (hZ : ∀ z : normalizer (K : Set G), z.val ∈ Z → coreAction K z = 1) :
    Section08.Source.starImage H K ≤
      centralizer (Section08.Source.starImage H Z : Set (Section08.Source.Hstar H)) := by
  let : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hn : (Section08.Source.starImage H K).Normal :=
    (inferInstance : (K.subgroupOf H).Normal).map _ (QuotientGroup.mk'_surjective _)
  apply le_centralizer_iff.mp
  rintro _ ⟨zH, hz, rfl⟩ _ ⟨kH, hk, rfl⟩
  let z : normalizer (K : Set G) := ⟨zH.val, hKn zH.property⟩
  let k : K := ⟨kH.val, hk⟩
  have he := congrArg (fun a : MulAut (K ⧸ pCore 2 K) => a (QuotientGroup.mk' (pCore 2 K) k))
    (hZ z hz)
  rw [coreAction_mk] at he
  change QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom z k) =
    QuotientGroup.mk' (pCore 2 K) k at he
  have hv := congrArg Subtype.val (congrArg (normalStarEquiv H K hKH hn) he)
  rw [normalStarEquiv_mk, normalStarEquiv_mk] at hv
  change QuotientGroup.mk' (pCore 2 H) (zH * kH * zH⁻¹) =
    QuotientGroup.mk' (pCore 2 H) kH at hv
  rw [map_mul, map_mul, map_inv] at hv
  exact (mul_inv_eq_iff_eq_mul.mp hv).symm

/-- Original13.7.5(7), with the literal two automizer maps and original covered choice of X. -/
theorem covered_component_automizers_ne
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h1339 : Section08.SolvableExclusion.Residual.Source1339
      L (sourceOne L T V₁) (plus L T V₁) T M V V₁)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hXK : plus L T V₁ ≤ K) (hout : ¬ sourceOne L T V₁ ≤ K) :
    ((sourceOne L T V₁).subgroupOf (normalizer (K : Set G))).map (coreAction K) ≠
      ((plus L T V₁).subgroupOf (normalizer (K : Set G))).map (coreAction K) := by
  intro heq
  have hKn := (component_normal_and_span_of_plus_le d hH hF9 hcover hKH hK hXK).1
  have hKM := normal_component_not_le_local d h1339 hH hKH hK hKn
  let J := sourceOne L T V₁
  let X := plus L T V₁
  let N := normalizer (K : Set G)
  have hJH : J ≤ H := le_sup_left.trans hH.1.2
  have hJN : J ≤ N := hJH.trans hKn
  have hXJ : X ≤ J := plus_le_one L T V₁ d.line_stable
  let f : J →* MulAut (K ⧸ pCore 2 K) := (coreAction K).comp (inclusion hJN)
  let C := f.ker.map J.subtype
  have hCJ : C ≤ J := map_subtype_le _
  have hCeq : C = J ⊓ (coreAction K).ker.map N.subtype := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.property, inclusion hJN j, hj, rfl⟩
    · rintro ⟨hx, n, hn, he⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      have en : inclusion hJN (⟨x, hx⟩ : J) = n := Subtype.ext he.symm
      change coreAction K (inclusion hJN ⟨x, hx⟩) = 1
      rw [en]
      exact hn
  have hkerN : N ≤ normalizer ((coreAction K).ker.map N.subtype : Set G) := by
    have hn := le_normalizer_map (H := (coreAction K).ker) N.subtype
    rw [normalizer_eq_top (H := (coreAction K).ker), ← MonoidHom.range_eq_map, range_subtype] at hn
    exact hn
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) := by
    rw [hCeq]
    exact (le_inf (T_normalizes_one L T V₁ d.line_stable)
      (((le_sup_right.trans hH.1.2).trans hKn).trans hkerN)).trans
        inf_normalizer_le_normalizer_inf
  have hLCJ : residual C ≤ J := (residual_le C).trans hCJ
  have hTLC : (T : Subgroup G) ≤ normalizer (residual C : Set G) :=
    hTC.trans (normalizer_le_residual_normalizer C)
  let : (X.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXJ).mpr (one_normalizes_plus L T V₁)
  have him : (X.subgroupOf J).map f = f.range := by
    apply le_antisymm (map_le_range _ _)
    rintro u ⟨j, rfl⟩
    have hu : f j ∈ (J.subgroupOf N).map (coreAction K) :=
      ⟨inclusion hJN j, j.property, rfl⟩
    rw [heq] at hu
    obtain ⟨n, hn, he⟩ := hu
    exact ⟨⟨n.val, hXJ hn⟩, hn, he⟩
  have hpX : IsPPerfect 2 (X.subgroupOf J) :=
    (residual_isPPerfect _).of_surjective (subgroupOfEquivOfLe hXJ).symm.toMonoidHom
      (subgroupOfEquivOfLe hXJ).symm.surjective
  have hs := sup_embedded_pResidual_kernel_eq_top 2 (X.subgroupOf J)
    (residual_isPPerfect _) hpX f him
  have hjoin := congrArg (map J.subtype) hs
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hXJ, map_embedded_pResidual,
    ← MonoidHom.range_eq_map, range_subtype] at hjoin
  change X ⊔ residual C = J at hjoin
  have hZC : zero L ≤ C := by
    rcases covered_point_subgroup_alternatives d hcover hLCJ
      (residual_isPPerfect C) hTLC with hb | hz | hx | hj
    · rw [hb, sup_bot_eq] at hjoin
      exact (hout (hjoin.symm.le.trans hXK)).elim
    · exact hz ▸ residual_le C
    · change residual C = X at hx
      rw [hx, sup_idem] at hjoin
      exact (hout (hjoin.symm.le.trans hXK)).elim
    · exact ((LocalAction.zero_le_one_of_factorization L T V₁
        (covered_factorization d hcover)).trans hj.symm.le).trans (residual_le C)
  have hZaction : ∀ z : N, z.val ∈ zero L → coreAction K z = 1 := by
    intro z hz
    obtain ⟨c, hc, he⟩ := hZC hz
    have he' : inclusion hJN c = z := Subtype.ext he
    change coreAction K (inclusion hJN c) = 1 at hc
    rwa [he'] at hc
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  exact zero_not_star_centralizing H K L T V₁ M hKH hJH d.normalizes_L
    (covered_factorization d hcover) (T.subtype hTH)
    (by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]) hKM
    (covered_zero_normalizer d h hcover)
    (star_centralizes_of_coreAction_eq_one hKH hKn hZaction)

/-- The two printed choices of X give the full original automizer conclusion. -/
theorem component_automizers_ne
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h1339 : Section08.SolvableExclusion.Residual.Source1339
      L (sourceOne L T V₁) (plus L T V₁) T M V V₁)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (X : Subgroup G)
    (hX : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = sourceOne L T V₁) ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁))
    (hXK : X ≤ K) (hout : ¬ sourceOne L T V₁ ≤ K) :
    ((sourceOne L T V₁).subgroupOf (normalizer (K : Set G))).map (coreAction K) ≠
      (X.subgroupOf (normalizer (K : Set G))).map (coreAction K) := by
  rcases hX with ⟨_, rfl⟩ | ⟨hc, rfl⟩
  · exact (hout hXK).elim
  · exact covered_component_automizers_ne d h h1339 hH hF9 hc hKH hK hXK hout

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
