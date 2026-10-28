module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
public import Theory.GroupTheory.SmallFittingResidual
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# The central cubic residual from the earlier Fitting alternative

We use the actual covered specialization of 13.8.14, expressed through
H → H/O₂(H). The natural local calculation makes L₁ solvable and
L₁/O₂(L₁) elementary of order nine. The quotient by the normal component
is solvable, so its centerless centralizer is solvable too. The small-Fitting
lemma puts L₁* inside K*F(H*); the contrary containment L₁ ≰ K therefore
forces F(H*) = X*. Its cubic order, normality and centralization follow.

This is a conditional deduction in Aschbacher–Smith 13.8.21(1), printed
p.957, using 13.2.2(3), 13.8.14 and normality from 13.8.16(1).
The input is the earlier Fitting alternative, not component centralization
or a product equivalence. Placement of the other marked direction follows
in the separate kernel calculation.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem star_le_of_le (H : Subgroup G) {A B : Subgroup G} (h : A ≤ B) :
    Source.starImage H A ≤ Source.starImage H B := map_mono (subgroupOf_mono H h)

omit [Finite G] in
theorem star_sup (H A B : Subgroup G) (hA : A ≤ H) (hB : B ≤ H) :
    Source.starImage H (A ⊔ B) = Source.starImage H A ⊔ Source.starImage H B := by
  unfold Source.starImage
  rw [subgroupOf_sup hA hB, Subgroup.map_sup]

omit [Finite G] in
theorem le_of_star_le (H K D : Subgroup G) [(K.subgroupOf H).Normal]
    (_hKH : K ≤ H) (hDH : D ≤ H) (hD : IsPPerfect 2 D)
    (hle : Source.starImage H D ≤ Source.starImage H K) : D ≤ K := by
  have hpre := comap_mono (f := QuotientGroup.mk' (pCore 2 H)) hle
  change ((D.subgroupOf H).map _).comap _ ≤ ((K.subgroupOf H).map _).comap _ at hpre
  rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk'] at hpre
  have hd := twoPerfect_le_of_le_sup_twoGroup (K.subgroupOf H) (D.subgroupOf H)
    (pCore 2 H) (hD.of_surjective (subgroupOfEquivOfLe hDH).symm.toMonoidHom
      (subgroupOfEquivOfLe hDH).symm.surjective) pCore_isPGroup (le_sup_left.trans hpre)
  intro d hdD
  exact hd (show (⟨d, hDH hdD⟩ : H) ∈ D.subgroupOf H from hdD)

private theorem solvable_join (D T : Subgroup G) (hD : Group.IsSolvable D)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (D : Set G)) : Group.IsSolvable (D ⊔ T : Subgroup G) := by
  let J := D ⊔ T
  let A := D.subgroupOf J
  let B := T.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hn)
  let : Group.IsSolvable D := hD
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show D ≤ J from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show D ≤ J from le_sup_left)).injective
  let : Group.IsSolvable T := @IsNilpotent.to_isSolvable T _ hT.isNilpotent
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show T ≤ J from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show T ≤ J from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A B
  rw [← subgroupOf_sup (show D ≤ J from le_sup_left) (show T ≤ J from le_sup_right)]
  exact subgroupOf_self _

omit [Finite G] in
private theorem star_component_quotient_solvable (H K D T : Subgroup G)
    [(Source.starImage H K).Normal]
    (hgen : H = K ⊔ (D ⊔ T)) (hKH : K ≤ H) (hDH : D ≤ H) (hTH : T ≤ H)
    (hsol : Group.IsSolvable (D ⊔ T : Subgroup G)) :
    Group.IsSolvable (Source.Hstar H ⧸ Source.starImage H K) := by
  let q := (QuotientGroup.mk' (Source.starImage H K)).comp (QuotientGroup.mk' (pCore 2 H))
  let f := q.comp (inclusion (sup_le hDH hTH))
  let : Group.IsSolvable (D ⊔ T : Subgroup G) := hsol
  apply Group.isSolvable_of_surjective (f := f)
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Source.starImage H K) y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) z
  have hj : (Source.starImage H K ⊔ Source.starImage H (D ⊔ T)) = ⊤ := by
    rw [← star_sup H K (D ⊔ T) hKH (sup_le hDH hTH), ← hgen]
    simp [Source.starImage, subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  obtain ⟨k, hk, d, hd, he⟩ := mem_sup_of_normal_left.mp
    (show QuotientGroup.mk' (pCore 2 H) h ∈ Source.starImage H K ⊔ Source.starImage H (D ⊔ T) by rw [hj]; trivial)
  obtain ⟨dH, hdH, rfl⟩ := hd
  refine ⟨⟨dH.val, hdH⟩, ?_⟩
  change QuotientGroup.mk' (Source.starImage H K) (QuotientGroup.mk' (pCore 2 H) dH) = _
  have hkq : QuotientGroup.mk' (Source.starImage H K) k = 1 :=
    (QuotientGroup.eq_one_iff k).mpr hk
  rw [← he, map_mul, hkq, one_mul]

omit [Finite G] in
theorem star_component_centerless (H K : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group) :
    center (Source.starImage H K) = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  have he : eK z ∈ center BinaryLinearThree.Group := (centerCongr eK ⟨z, hz⟩).property
  rw [Matrix.PSL3Two.center_eq_bot, mem_bot] at he
  exact eK.injective (he.trans eK.map_one.symm)

/-- Consequence of the covered specialization of the earlier Fitting alternative
13.8.14. The external residual forces the nontrivial alternative; normality,
cubic order and centralization are deductions. -/
theorem component_centralization (H K L T V V₁ V₃ : Subgroup G)
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (one L T V₁ ⊔ T))
    (hnot : ¬ one L T V₁ ≤ K)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (hfit : fittingSubgroup (Source.Hstar H) = ⊥ ∨
      fittingSubgroup (Source.Hstar H) = Source.starImage H (plus L T V₁)) :
    fittingSubgroup (Source.Hstar H) = Source.starImage H (plus L T V₁) ∧
    (Source.starImage H (plus L T V₁)).Normal ∧
    Nat.card (Source.starImage H (plus L T V₁)) = 3 ∧
    Source.starImage H (one L T V₁) ≤ Source.starImage H K ⊔ Source.starImage H (plus L T V₁) ∧
    Source.starImage H K ≤ centralizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)) := by
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hDH : one L T V₁ ≤ H := by rw [hgen]; exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  have hXH := (plus_le_one L T V₁ d.line_stable).trans hDH
  let : (Source.starImage H K).Normal :=
    (inferInstance : (K.subgroupOf H).Normal).map _ (QuotientGroup.mk'_surjective _)
  have hpD : IsPPerfect 2 (Source.starImage H (one L T V₁)) :=
    (residual_isPPerfect _).of_surjective (starMap H _ hDH) (starMap_surjective H _ hDH)
  have hfc : Nat.card (fittingSubgroup (Source.Hstar H)) = 1 ∨
      Nat.card (fittingSubgroup (Source.Hstar H)) = 3 := by
    rcases hfit with hf | hf
    · exact Or.inl (by rw [hf, card_bot])
    · have hn : (Source.starImage H (plus L T V₁)).Normal := hf ▸ inferInstance
      exact Or.inr (hf ▸ normal_star_card_three H _ hXH hn (d.plus_core_card hfactor))
  have ho : IsPGroup 2 (MulAut.Outer (Source.starImage H K)) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv (MulAut.outerCongr eK).symm
  have hsD : Group.IsSolvable (one L T V₁) := by
    let : IsMulCommutative (one L T V₁ ⧸ pCore 2 (one L T V₁)) := d.one_quotient_commutative hfactor
    exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (one L T V₁))).mpr
      ⟨@IsNilpotent.to_isSolvable _ _ pCore_isPGroup.isNilpotent,
        Group.isSolvable_of_comm (fun a b => mul_comm a b)⟩
  have hT : IsPGroup 2 T := d.sylow_eq ▸ d.sylow.isPGroup' |>.of_equiv
    (subgroupOfEquivOfLe (show T ≤ L ⊔ T from le_sup_right))
  let : Group.IsSolvable (Source.Hstar H ⧸ Source.starImage H K) :=
    star_component_quotient_solvable H K _ T hgen hKH hDH hTH
      (solvable_join _ _ hsD hT (T_normalizes_one L T V₁ d.line_stable))
  have hDC := twoPerfect_le_normal_sup_fitting (Source.starImage H K) _ hpD ho
    (centralizer_solvable_of_centerless_quotient _ (star_component_centerless H K eK)) hfc
  have hf : fittingSubgroup (Source.Hstar H) = Source.starImage H (plus L T V₁) := by
    rcases hfit with hf | hf
    · rw [hf, sup_bot_eq] at hDC
      exact (hnot (le_of_star_le H K _ hKH hDH (residual_isPPerfect _) hDC)).elim
    · exact hf
  have hn : (Source.starImage H (plus L T V₁)).Normal := hf ▸ inferInstance
  have hc := normal_star_card_three H _ hXH hn (d.plus_core_card hfactor)
  refine ⟨hf, hn, hc, by simpa only [hf] using hDC, ?_⟩
  have hpK : IsPPerfect 2 (Source.starImage H K) := by
    let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
    let : IsSimpleGroup BinaryLinearThree.Group := Matrix.PSL3Two.equiv.isSimpleGroup
    let : IsSimpleGroup (Source.starImage H K) := eK.isSimpleGroup
    intro N hN hQ
    rcases hN.eq_bot_or_eq_top with he | he
    · have htwo : IsPGroup 2 (Source.starImage H K) := hQ.of_equiv
        ((QuotientGroup.quotientMulEquivOfEq he).trans QuotientGroup.quotientBot)
      have hdiv := htwo.exists_card_eq
      obtain ⟨n, hn⟩ := hdiv
      have h168 : Nat.card (Source.starImage H K) = 168 :=
        (Nat.card_congr eK.toEquiv).trans Matrix.PSL3Two.card_SL
      have h3 : 3 ∣ 2 ^ n := by rw [← hn, h168]; decide
      have := Nat.prime_three.dvd_of_dvd_pow h3
      norm_num at this
    · exact he
  exact twoPerfect_centralizes_small_normal _ _ hpK (Or.inr hc)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
