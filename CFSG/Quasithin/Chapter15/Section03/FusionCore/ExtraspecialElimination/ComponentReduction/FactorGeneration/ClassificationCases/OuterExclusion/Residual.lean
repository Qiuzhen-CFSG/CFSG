module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.SaturatedLift
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.RankTwoAction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Residual and seed restrictions on the outer alternatives

A normal subgroup R of order three in H* is centralized by the two-perfect
Y₀*. Its full inverse image in H therefore lies in N_G(Y₀) = M, by the
residual-normalizer argument. Lifting cubic elements gives R ≤ Y₀*.
Since A* lies in O₂(Y₀*T*), it centralizes R. Normality of R then makes
the entire selected conjugate span J* centralize R. In particular, an
order-three core of J* must be central; the A₆ × C₃ outer extension will
contradict this conclusion.

Separately, a cubic subgroup fixing the image of every element of Z_S
has its full inverse image in N_G(Z_S) ≤ M. The same cubic lifting puts
it in Y₀*. This is a necessary restriction for the remaining symmetric
and G₂(2) cases. It does not assert that Y₀* is abelian or that those
cases have been excluded.

All normality used in H is relative. The quotient is the literal H/O₂(H),
and the seed action is the actual SectionAction on localSpan Z_S H / Z.
The results use a sufficient subset of the earlier local hypotheses;
no strong offender or component-generation assertion is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(i), printed pp.1143–1144, and B.5.6, printed p.105.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.OuterExclusion
variable {G : Type*} [Group G]

private theorem centralizes_three_of_twoPerfect [Finite G]
    (R Y : Subgroup G) (hR : Nat.card R = 3)
    (hY : IsPPerfect 2 Y) (hn : Y ≤ normalizer (R : Set G)) :
    Y ≤ centralizer (R : Set G) := by
  let : IsCyclic R := isCyclic_of_prime_card hR
  have hp : IsPGroup 2 (MulAut R) := IsPGroup.of_card (n := 1) (by
    rw [IsCyclic.card_mulAut, hR]
    decide)
  let f : Y →* MulAut R := R.normalizerMonoidHom.comp (inclusion hn)
  have hq : IsPGroup 2 (Y ⧸ f.ker) :=
    (hp.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hk := hY f.ker inferInstance hq
  intro y hy r hr
  have hf : f ⟨y, hy⟩ = 1 := by
    exact MonoidHom.mem_ker.mp (show (⟨y, hy⟩ : Y) ∈ f.ker by rw [hk]; trivial)
  have he := congrArg (fun a : MulAut R => ((a ⟨r, hr⟩ : R) : G)) hf
  change y * r * y⁻¹ = r at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Every normal cubic subgroup of the star quotient lies in the source residual. -/
theorem normal_three_le_star_residual [Finite G]
    (H M Y0 : Subgroup G) (hYH : Y0 ≤ H) (hY : IsPPerfect 2 Y0)
    (hN : normalizer (Y0 : Set G) = M) (hQM : localTwoCore H ≤ M)
    (hθ : theta (M ⊓ H) = Y0)
    (R : Subgroup (H ⧸ pCore 2 H)) [R.Normal] (hR : Nat.card R = 3) :
    R ≤ starImage H Y0 := by
  let L := saturatedStarLift H H R
  have hRH : R ≤ starImage H H := by
    change R ≤ (H.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
    rw [subgroupOf_self, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    exact le_top
  have hLH : L ≤ H := saturatedStarLift_le_overgroup H H R
  have hstar : starImage H L = R := saturatedStarLift_image H H R hRH
  have hsub : (L.subgroupOf H).IsSubnormal := by
    rw [saturatedStarLift_subgroupOf, subgroupOf_self, top_inf_eq]
    exact (inferInstance : (R.comap (QuotientGroup.mk' (pCore 2 H))).Normal).isSubnormal
  have hnorm : Y0 ≤ normalizer (L : Set G) := by
    apply normalizes_saturated_of_star_normalizes H H L Y0 hLH hYH hLH
      (saturatedStarLift_kernel_le H H R) (hYH.trans H.le_normalizer)
    rw [hstar, R.normalizer_eq_top]
    exact le_top
  have hc : ⁅starImage H L, starImage H Y0⁆ = ⊥ := by
    rw [hstar, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (centralizes_three_of_twoPerfect R _ hR (starImage_twoPerfect H Y0 hYH hY)
        (by rw [R.normalizer_eq_top]; exact le_top))
  have hLM : L ≤ M := le_M_of_commutator_le_twoCore H M Y0 L hY hN hLH hsub hQM
    (commutator_le_twoCore_of_star_commutes H L Y0 hLH hYH hnorm hc)
  by_contra hnot
  exact theta_escape_of_star_three_subgroup H L Y0 hLH R hR (le_of_eq hstar.symm) hnot
    ((theta_mono (le_inf hLM hLH)).trans_eq hθ)

/-- The selected span centralizes every normal cubic subgroup of the star quotient. -/
theorem normal_three_centralizes_star_span [Finite G]
    (H M Y0 T A : Subgroup G) (hAH : A ≤ H) (hYH : Y0 ≤ H)
    (hY : IsPPerfect 2 Y0) (hN : normalizer (Y0 : Set G) = M)
    (hQM : localTwoCore H ≤ M) (hθ : theta (M ⊓ H) = Y0)
    (hA : starImage H A ≤
      (pCore 2 ↥(starImage H Y0 ⊔ starImage H T)).map
        (starImage H Y0 ⊔ starImage H T).subtype)
    (R : Subgroup (H ⧸ pCore 2 H)) [R.Normal] (hR : Nat.card R = 3) :
    starImage H (localSpan A H) ≤ centralizer (R : Set (H ⧸ pCore 2 H)) := by
  let B := starImage H Y0 ⊔ starImage H T
  let Q := (pCore 2 B).map B.subtype
  have hRB : R ≤ B := (normal_three_le_star_residual H M Y0 hYH hY hN hQM hθ R hR).trans le_sup_left
  have hRQ : ⁅R, starImage H A⁆ ≤ Q := by
    apply (commutator_mono hRB hA).trans
    exact le_normalizer_iff_commutator_le_right.mp
      (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hd : Disjoint R Q :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hR)).disjoint_of_coprime
      (pCore_isPGroup.map B.subtype) (by decide)
  have hc : ⁅R, starImage H A⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf (commutator_le_left R _) hRQ).trans hd.le_bot
  have hAC : starImage H A ≤ centralizer (R : Set (H ⧸ pCore 2 H)) := by
    rw [commutator_comm] at hc
    exact commutator_eq_bot_iff_le_centralizer.mp hc
  let C := centralizer (R : Set (H ⧸ pCore 2 H))
  let D := (C.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype
  have hnD : H ≤ normalizer (D : Set G) := by
    have hC : C.Normal := inferInstance
    have hn := (C.comap (QuotientGroup.mk' (pCore 2 H))).le_normalizer_map H.subtype
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hAD : A ≤ D := by
    intro a ha
    exact ⟨⟨a, hAH ha⟩, hAC ⟨⟨a, hAH ha⟩, ha, rfl⟩, rfl⟩
  have hJD := conjugateSpanBy_le hAD hnD
  rintro x ⟨j, hj, rfl⟩
  obtain ⟨d, hd, he⟩ := hJD hj
  have hed : d = j := Subtype.ext he
  exact hed ▸ hd

/-- A three-core of order three in the selected star span must be central. -/
theorem threeCore_le_center_of_card_three [Finite G]
    (H M Y0 T A : Subgroup G) (hAH : A ≤ H) (hYH : Y0 ≤ H)
    (hY : IsPPerfect 2 Y0) (hN : normalizer (Y0 : Set G) = M)
    (hQM : localTwoCore H ≤ M) (hθ : theta (M ⊓ H) = Y0)
    (hA : starImage H A ≤
      (pCore 2 ↥(starImage H Y0 ⊔ starImage H T)).map
        (starImage H Y0 ⊔ starImage H T).subtype)
    (hcard : Nat.card (pCore 3 (starImage H (localSpan A H))) = 3) :
    pCore 3 (starImage H (localSpan A H)) ≤ center (starImage H (localSpan A H)) := by
  let J := starImage H (localSpan A H)
  let R := (pCore 3 J).map J.subtype
  have hJ : J.Normal := (localSpan_normal A H hAH).map _ (QuotientGroup.mk'_surjective _)
  have hR : R.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    calc
      ⊤ = normalizer (J : Set (H ⧸ pCore 2 H)) := J.normalizer_eq_top.symm
      _ ≤ normalizer (R : Set (H ⧸ pCore 2 H)) :=
        normalizer_le_normalizer_characteristic_image J (pCore 3 J)
  have hc := normal_three_centralizes_star_span H M Y0 T A hAH hYH hY hN hQM hθ hA R
    ((card_map_of_injective J.subtype_injective).trans hcard)
  intro r hr
  rw [mem_center_iff]
  intro j
  apply Subtype.ext
  exact (hc j.property r (mem_map_of_mem J.subtype hr)).symm

/-- Cubic subgroups fixing the actual seed section lie in the source residual. -/
theorem three_subgroup_le_residual_of_fixed_seed [Finite G]
    (H M ZS Z Y0 : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hZ : Z ≤ ZS) (hseedN : normalizer (ZS : Set G) ≤ M)
    (hθ : theta (M ⊓ H) = Y0)
    (R : Subgroup (H ⧸ pCore 2 H)) (hR : Nat.card R = 3)
    (hfixed : ∀ z : ZS,
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
        ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩) ∈
          Representation.BinaryOffender.fixedSpace action.representation R) :
    R ≤ starImage H Y0 := by
  let L := saturatedStarLift H H R
  have hRH : R ≤ starImage H H := by
    change R ≤ (H.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
    rw [subgroupOf_self, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    exact le_top
  have hLH : L ≤ H := saturatedStarLift_le_overgroup H H R
  have hstar : starImage H L = R := saturatedStarLift_image H H R hRH
  have hLM : L ≤ M := (normalizes_seed_of_fixed_image H ZS Z L action hZ hLH
    (by simpa only [hstar] using hfixed)).trans hseedN
  by_contra hnot
  exact theta_escape_of_star_three_subgroup H L Y0 hLH R hR (le_of_eq hstar.symm) hnot
    ((theta_mono (le_inf hLM hLH)).trans_eq hθ)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.OuterExclusion
