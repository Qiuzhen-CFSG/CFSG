module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.DiagramAction.CubicLifts
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.PairGeometry
public import Theory.GroupTheory.FrattiniRankTwoShadow
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions

/-!
# Actual binary component actions from invariant cubic residuals

Two individually invariant, two-perfect subgroups with cubic two-core
quotients and join quotient of order nine determine two actual minimal
parabolics over the component Sylow subgroup. The checked common-coordinate
construction supplies their bases and distinctness. Inner/inverse-transpose
coverage then shows that the original conjugation action is inner.

The order calculation below gives the three-part bound required to lift
these cubic residuals from the source rank-two shadow. It uses the genuine
binary matrix equivalences, without assuming a flag marking or innerness.

The final assembly uses this bound to prove that the Frattini subgroup of
the two-core quotient is trivial. Thus the source O_{2,Φ} shadow becomes
an actual O₂ quotient. Lifting its two normal cubic axes supplies the
invariant residuals, so every element of S induces an inner automorphism
of D. No fixed nodes or component equality with the ambient group are
assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of the proof of 15.3.35, printed p.1139; normalization comes from
15.3.11(4), printed p.1123. Common flag geometry is the intrinsic binary
calculation also used in 13.8.25, printed pp.959--960.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition.DiagramAction
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource

private theorem model_inner_of_cubic_pair {m : ℕ} (hm : m = 3 ∨ m = 4)
    (U : Sylow 2 (LinearGroup (m + 1))) (A B : Subgroup (LinearGroup (m + 1)))
    (ha : IsPPerfect 2 A) (hb : IsPPerfect 2 B)
    (hna : (U : Subgroup (LinearGroup (m + 1))) ≤ normalizer (A : Set (LinearGroup (m + 1))))
    (hnb : (U : Subgroup (LinearGroup (m + 1))) ≤ normalizer (B : Set (LinearGroup (m + 1))))
    (hca : Nat.card (A ⧸ pCore 2 A) = 3) (hcb : Nat.card (B ⧸ pCore 2 B) = 3)
    (hcab : Nat.card ((A ⊔ B : Subgroup _) ⧸ pCore 2 (A ⊔ B : Subgroup _)) = 9)
    (a : MulAut (LinearGroup (m + 1)))
    (hA : A.map a.toMonoidHom = A) (hB : B.map a.toMonoidHom = B)
    (hU : (U : Subgroup _).map a.toMonoidHom = U) :
    a ∈ MulAut.innerSubgroup _ := by
  have hmark : ∃ (b : Basis m) (i j : Fin m),
      A ⊔ (U : Subgroup _) = minimalParabolic b i ∧
      B ⊔ (U : Subgroup _) = minimalParabolic b j ∧
      A ⊔ (U : Subgroup _) ≠ B ⊔ U := by
    rcases hm with rfl | rfl
    · obtain ⟨b, i, j, _, hAi, hBj, _, _, _, _, _, _, _, _, _, _, hne⟩ :=
        PairGeometry.four_common_coordinates U A B ha hb hna hnb hca hcb hcab
      exact ⟨b, i, j, hAi, hBj, hne⟩
    · obtain ⟨b, i, j, _, hAi, hBj, _, _, _, _, _, _, _, _, _, hne⟩ :=
        PairGeometry.five_common_coordinates U A B ha hb hna hnb hca hcb hcab
      exact ⟨b, i, j, hAi, hBj, hne⟩
  obtain ⟨b, i, j, hAi, hBj, hne⟩ := hmark
  apply preserving_two_minimalParabolics_is_inner (by omega) (by omega) b b i j U
    (hAi ▸ le_sup_right) (hBj ▸ le_sup_right) (by rwa [← hAi, ← hBj]) a
  · rw [← hAi, Subgroup.map_sup, hA, hU]
  · rw [← hBj, Subgroup.map_sup, hB, hU]



private theorem map_congr_action {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) (a : MulAut G) :
    (A.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom =
      (A.map a.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  change e (a (e.symm (e x))) = e (a x)
  rw [e.symm_apply_apply]

private theorem core_quotient_card_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) :
    Nat.card (A.map e.toMonoidHom ⧸ pCore 2 (A.map e.toMonoidHom)) =
      Nat.card (A ⧸ pCore 2 A) :=
  (Nat.card_congr (QuotientGroup.congr _ _ (e.subgroupMap A)
    (pCore_map_iso 2 (e.subgroupMap A))).toEquiv).symm

private theorem inner_of_equiv_cubic_pair {G : Type*} [Group G] [Finite G]
    {m : ℕ} (hm : m = 3 ∨ m = 4) (e : G ≃* LinearGroup (m + 1))
    (U : Sylow 2 G) (A B : Subgroup G)
    (ha : IsPPerfect 2 A) (hb : IsPPerfect 2 B)
    (hna : (U : Subgroup G) ≤ normalizer (A : Set G))
    (hnb : (U : Subgroup G) ≤ normalizer (B : Set G))
    (hca : Nat.card (A ⧸ pCore 2 A) = 3) (hcb : Nat.card (B ⧸ pCore 2 B) = 3)
    (hcab : Nat.card ((A ⊔ B : Subgroup G) ⧸ pCore 2 (A ⊔ B : Subgroup G)) = 9)
    (a : MulAut G) (hA : A.map a.toMonoidHom = A) (hB : B.map a.toMonoidHom = B)
    (hU : (U : Subgroup G).map a.toMonoidHom = U) :
    a ∈ MulAut.innerSubgroup G := by
  let V := U.mapSurjective (f := e.toMonoidHom) e.surjective
  have hnA : (V : Subgroup (LinearGroup (m + 1))) ≤ normalizer (A.map e.toMonoidHom : Set (LinearGroup (m + 1))) := by
    exact (Subgroup.map_mono hna).trans (Subgroup.le_normalizer_map _)
  have hnB : (V : Subgroup (LinearGroup (m + 1))) ≤ normalizer (B.map e.toMonoidHom : Set (LinearGroup (m + 1))) := by
    exact (Subgroup.map_mono hnb).trans (Subgroup.le_normalizer_map _)
  have hcAB : Nat.card ((A.map e.toMonoidHom ⊔ B.map e.toMonoidHom : Subgroup _) ⧸
      pCore 2 (A.map e.toMonoidHom ⊔ B.map e.toMonoidHom : Subgroup _)) = 9 := by
    rw [← Subgroup.map_sup, core_quotient_card_map, hcab]
  have hi := model_inner_of_cubic_pair hm V (A.map e.toMonoidHom) (B.map e.toMonoidHom)
    (ha.of_surjective (e.subgroupMap A).toMonoidHom (e.subgroupMap A).surjective)
    (hb.of_surjective (e.subgroupMap B).toMonoidHom (e.subgroupMap B).surjective)
    hnA hnB ((core_quotient_card_map e A).trans hca)
    ((core_quotient_card_map e B).trans hcb) hcAB (MulAut.congr e a)
    (by rw [map_congr_action, hA]) (by rw [map_congr_action, hB])
    (by change ((U : Subgroup G).map e.toMonoidHom).map _ = _
        rw [map_congr_action, hU]
        rfl)
  rw [← MulAut.map_innerSubgroup_congr e, Subgroup.mem_map_equiv] at hi
  simpa only [MulEquiv.symm_apply_apply] using hi

/-- Two normalized cubic residuals construct the actual fixed parabolics.
The individual preservation statements concern conjugation on D itself. -/
theorem inner_of_cubic_pair {X : Type*} [Group X] [Finite X]
    (D S : Subgroup X) [D.Normal] (hmodel : SmallBinaryModel D)
    (hS : ∃ U : Sylow 2 X, (U : Subgroup X) = S)
    (A B : Subgroup D) (ha : IsPPerfect 2 A) (hb : IsPPerfect 2 B)
    (hca : Nat.card (A ⧸ pCore 2 A) = 3) (hcb : Nat.card (B ⧸ pCore 2 B) = 3)
    (hcab : Nat.card ((A ⊔ B : Subgroup D) ⧸ pCore 2 (A ⊔ B : Subgroup D)) = 9)
    (hA : ∀ s ∈ S, A.map (MulAut.conjNormal s).toMonoidHom = A)
    (hB : ∀ s ∈ S, B.map (MulAut.conjNormal s).toMonoidHom = B) :
    ∀ s ∈ S, MulAut.conjNormal (H := D) s ∈ MulAut.innerSubgroup D := by
  obtain ⟨U, rfl⟩ := hS
  obtain ⟨T, hT⟩ := U.exists_subgroupOf_eq_of_normal D
  have hnA : (T : Subgroup D) ≤ normalizer (A : Set D) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    simpa only [MulAut.conjNormal_val, MulEquiv.toMonoidHom_eq_coe] using hA (x : X) (show x ∈ (U : Subgroup X).subgroupOf D from hT ▸ hx)
  have hnB : (T : Subgroup D) ≤ normalizer (B : Set D) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    simpa only [MulAut.conjNormal_val, MulEquiv.toMonoidHom_eq_coe] using hB (x : X) (show x ∈ (U : Subgroup X).subgroupOf D from hT ▸ hx)
  intro s hs
  have hTs : (T : Subgroup D).map (MulAut.conjNormal s).toMonoidHom = T := by
    rw [hT]
    ext x
    rw [Subgroup.mem_map_equiv]
    change ((MulAut.conjNormal s).symm x : X) ∈ (U : Subgroup X) ↔ (x : X) ∈ U
    rw [MulAut.conjNormal_symm_apply]
    constructor
    · intro hx
      change (x : X) ∈ (U : Subgroup X)
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using
        (U : Subgroup X).mul_mem ((U : Subgroup X).mul_mem hs hx) ((U : Subgroup X).inv_mem hs)
    · intro hx
      exact (U : Subgroup X).mul_mem ((U : Subgroup X).mul_mem
        ((U : Subgroup X).inv_mem hs) hx) hs
  obtain ⟨n, hn, ⟨e⟩⟩ := smallBinaryModel_linear hmodel
  rcases hn with rfl | rfl
  · exact inner_of_equiv_cubic_pair (m := 3) (Or.inl rfl) e T A B ha hb hnA hnB
      hca hcb hcab _ (hA s hs) (hB s hs) hTs
  · exact inner_of_equiv_cubic_pair (m := 4) (Or.inr rfl) e T A B ha hb hnA hnB
      hca hcb hcab _ (hA s hs) (hB s hs) hTs

private theorem linear_three_part (n : ℕ) (hn : n = 4 ∨ n = 5) :
    (Nat.card (LinearGroup n)).factorization 3 = 2 := by
  have hc : Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
    rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
    simp
  rw [hc]
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ]
  · rw [show 20160 = 3 ^ 2 * 2240 from rfl]
    rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2240),
      Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_three]
  · rw [show 9999360 = 3 ^ 2 * 1111040 from rfl]
    rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 1111040),
      Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_three]

/-- Both binary models have three-part nine. This is an order calculation,
not a simplicity or recognition assumption. -/
theorem smallBinaryModel_three_part {G : Type*} [Group G]
    (hmodel : SmallBinaryModel G) : (Nat.card G).factorization 3 = 2 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := smallBinaryModel_linear hmodel
  rw [Nat.card_congr e.toEquiv]
  exact linear_three_part n hn

/-- A normalized Sylow supplement contributes no factor of three, so the
rank-two shadow subgroup has three-part at most nine. -/
theorem join_three_part_le {X : Type*} [Group X] [Finite X]
    (D Y S : Subgroup X) (hmodel : SmallBinaryModel D)
    (hY : Y ≤ D) (hS : IsPGroup 2 S) (hn : S ≤ normalizer (Y : Set X)) :
    (Nat.card (Y ⊔ S : Subgroup X)).factorization 3 ≤ 2 := by
  rw [CubicPairGeometry.normalized_join_three_part Y S hS hn,
    ← smallBinaryModel_three_part hmodel]
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
    (card_dvd_of_le hY) 3

/-- The actual local configuration supplies every input to the order bound;
normalization is retained separately, as in source 15.3.11(4). -/
theorem localConfiguration_three_part_le {X : Type*} [Group X] [Finite X]
    (D M Y S : Subgroup X) (hmodel : SmallBinaryModel D)
    (hlocal : LocalConfiguration D M Y S) (hn : S ≤ normalizer (Y : Set X)) :
    (Nat.card (Y ⊔ S : Subgroup X)).factorization 3 ≤ 2 := by
  obtain ⟨U, hU⟩ := hlocal.sylow
  exact join_three_part_le D Y S hmodel (hlocal.yplus_le.trans inf_le_right)
    (hU ▸ U.isPGroup') hn

/-- The intrinsic action conclusion in the last paragraph of 15.3.35.
The source local configuration and normalization construct two individually
fixed minimal parabolics, excluding inverse transpose from the actual
conjugation action on D. The displayed ambient hypotheses retain the
source component setup; the argument only needs normality, the binary
model, the local configuration and normalization. -/
theorem inner_of_localConfiguration {X : Type*} [Group X] [Finite X]
    (D M Y S : Subgroup X) [D.Normal] [IsSimpleGroup D] [Group.IsPerfect D]
    (_hF : Theory.GroupTheory.generalizedFitting X = D)
    (_hc : centralizer (D : Set X) = ⊥) (_hgen : D ⊔ S = ⊤)
    (hmodel : SmallBinaryModel D) (hlocal : LocalConfiguration D M Y S)
    (hn : S ≤ normalizer (Y : Set X)) :
    ∀ s ∈ S, MulAut.conjNormal (H := D) s ∈ MulAut.innerSubgroup D := by
  have he := FrattiniRankTwoShadow.quotient_twoCore_equiv hlocal.shadow
    (localConfiguration_three_part_le D M Y S hmodel hlocal hn)
  obtain ⟨U, hU⟩ := hlocal.sylow
  obtain ⟨A, B, ha, hb, hca, hcb, hcab, hA, hB⟩ :=
    CubicLifts.exists_invariant_cubic_pair D Y S
      (hlocal.yplus_le.trans inf_le_right) (hU ▸ U.isPGroup') hn he
  exact inner_of_cubic_pair D S hmodel hlocal.sylow A B ha hb hca hcb hcab hA hB

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition.DiagramAction
