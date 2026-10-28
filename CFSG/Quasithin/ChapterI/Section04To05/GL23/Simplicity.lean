module
public import CFSG.Quasithin.ChapterI.Section04To05.GL23.Basic
public import Theory.SpecificGroups.GL2.ThreeInvolutionNormalSubgroups
public import ABG.ChapterII.Section1.Center
public import Theory.GroupTheory.FourGroupCentralizerOddCore

/-!
# Simplicity from the GL₂(3) involution centralizer

An even normal subgroup contains all involutions by fusion. The involutions
normally generate its intersection with C_G(z), so it contains C_G(z) and
an ambient Sylow subgroup. That Sylow's center has order two; its normalizer
fixes z. Frattini's argument now makes the normal subgroup all of G.

For an odd normal subgroup N, C_N(u) is trivial at every involution, since
GL₂(3) has no nontrivial odd normal subgroup. Each involution therefore
inverts N. Two commuting involutions and their product inside the local
matrix group force N to be trivial. These arguments remove the simplicity
hypothesis before applying Wong's recognition results.

Source: Aschbacher–Smith I.4.2, printed p.416, and Wong's Theorem 6.
-/

namespace CFSG.Quasithin.GL23InvolutionCentralizerHypotheses
open Subgroup Matrix.GeneralLinearGroup
variable {G : Type*} [Group G] [Finite G]

private theorem normal_odd_centralizer (h : GL23InvolutionCentralizerHypotheses G)
    (N : Subgroup G) [N.Normal] (ho : Odd (Nat.card N))
    (u : G) (hu : orderOf u = 2) {x : G} (hx : x ∈ N)
    (hc : x * u = u * x) : x = 1 := by
  let C := centralizer ({u} : Set G)
  let D := N.subgroupOf C
  let e := (h.centralizer_zmod_equiv u hu).some
  let f : D →* N := {
    toFun := fun a => ⟨a.val.val, a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun n : N => (n : G)) hab
  have hDodd : Odd (Nat.card D) := Nat.not_even_iff_odd.mp (by
    intro hd
    exact ho.not_two_dvd_nat ((even_iff_two_dvd.mp hd).trans (card_dvd_of_injective f hf)))
  let E := D.map e.toMonoidHom
  let : E.Normal := (inferInstance : D.Normal).map _ e.surjective
  have hEodd : Odd (Nat.card E) := by
    rw [← Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
    exact hDodd
  have heq : E = ⊥ := three_odd_normal_eq_bot E hEodd
  let xC : C := ⟨x, mem_centralizer_singleton_iff.mpr hc⟩
  have hxD : xC ∈ D := hx
  have hh : e xC ∈ E := mem_map_of_mem _ hxD
  rw [heq] at hh
  have hxC : xC = 1 := e.injective (hh.trans e.map_one.symm)
  exact congrArg Subtype.val hxC

/-- Every odd normal subgroup is trivial under the I.4.2 hypotheses. -/
public theorem odd_normal_eq_bot (h : GL23InvolutionCentralizerHypotheses G)
    (N : Subgroup G) [N.Normal] (ho : Odd (Nat.card N)) : N = ⊥ := by
  let e := (h.centralizer_zmod_equiv h.z h.involution).some
  let f : GL (Fin 2) (ZMod 3) →* G :=
    (centralizer ({h.z} : Set G)).subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  let a := f threeCentral
  let b := f threeReflection
  have ha : orderOf a = 2 :=
    (orderOf_injective f hf _).trans (three_conjugacy_data.2.1 1)
  have hb : orderOf b = 2 :=
    (orderOf_injective f hf _).trans (three_conjugacy_data.2.1 5)
  have hab : orderOf (a * b) = 2 := by
    change orderOf (f threeCentral * f threeReflection) = 2
    rw [← map_mul, orderOf_injective f hf]
    apply orderOf_eq_prime
    · decide +kernel
    · decide +kernel
  have hfusion (u v : G) (hu : orderOf u = 2) (hv : orderOf v = 2) : IsConj u v :=
    (isConj_iff.mpr (h.involutions_conjugate u hu)).trans
      (isConj_iff.mpr (h.involutions_conjugate v hv)).symm
  apply normal_eq_bot_of_fused_triple a b ha (hfusion a b ha hb) (hfusion a (a * b) ha hab) N
  intro x hx hc
  exact h.normal_odd_centralizer N ho a ha hx (mem_centralizer_singleton_iff.mp hc)

private theorem normal_contains_involutions (h : GL23InvolutionCentralizerHypotheses G)
    (N : Subgroup G) [N.Normal] (heven : 2 ∣ Nat.card N)
    (x : G) (hx : x ^ 2 = 1) : x ∈ N := by
  by_cases hx1 : x = 1
  · exact hx1 ▸ N.one_mem
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 heven
  have huG : orderOf (u : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hu
  obtain ⟨g, hg⟩ := h.involutions_conjugate u huG
  have hzN : h.z ∈ N := hg ▸ (inferInstance : N.Normal).conj_mem u u.property g
  obtain ⟨k, hk⟩ := h.involutions_conjugate x (orderOf_eq_prime hx hx1)
  have hxN := (inferInstance : N.Normal).conj_mem h.z hzN k⁻¹
  simpa only [← hk, inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hxN

/-- Every even normal subgroup is the whole group under the I.4.2 hypotheses. -/
public theorem even_normal_eq_top (h : GL23InvolutionCentralizerHypotheses G)
    (N : Subgroup G) [N.Normal] (heven : 2 ∣ Nat.card N) : N = ⊤ := by
  let C := centralizer ({h.z} : Set G)
  let D := N.subgroupOf C
  let e := (h.centralizer_zmod_equiv h.z h.involution).some
  let E := D.map e.toMonoidHom
  let : E.Normal := (inferInstance : D.Normal).map _ e.surjective
  have hE : E = ⊤ := three_normal_eq_top_of_involutions E (by
    intro x hx
    have hx2 : (e.symm x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    have hN : (e.symm x : G) ∈ N := h.normal_contains_involutions N heven _
      (congrArg Subtype.val hx2)
    exact ⟨e.symm x, hN, e.apply_symm_apply x⟩)
  have hCN : C ≤ N := by
    intro x hx
    have hh : e ⟨x,hx⟩ ∈ E := hE ▸ mem_top _
    obtain ⟨y, hy, he⟩ := hh
    have hyx : (y : G) = x := congrArg Subtype.val (e.injective he)
    exact hyx ▸ (show (y : G) ∈ N from hy)
  obtain ⟨S, hSC⟩ := h.exists_sylow_le_centralizer
  have hzS : h.z ∈ (S : Subgroup G) := by
    have hzC : h.z ∈ C := mem_centralizer_singleton_iff.mpr rfl
    have hZ : IsPGroup 2 (zpowers (⟨h.z,hzC⟩ : C)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,
        ← Subgroup.orderOf_coe, h.involution]; norm_num)
    have hcentral : zpowers (⟨h.z,hzC⟩ : C) ≤ center C :=
      zpowers_le.mpr (mem_center_iff.mpr (fun a =>
        Subtype.ext (mem_centralizer_singleton_iff.mp a.property)))
    have hnormal : (zpowers (⟨h.z,hzC⟩ : C)).Normal := ⟨fun x hx g => by
      have hc := mem_center_iff.mp (hcentral hx) g
      simpa only [hc, mul_inv_cancel_right] using hx⟩
    let := hnormal
    have hle := hZ.le_sylow_of_normal (S.subtype hSC)
    exact hle (mem_zpowers _)
  let zS : S := ⟨h.z, hzS⟩
  have hzcenter : zS ∈ center S := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hSC x.property)))
  have hNS : normalizer (S : Set G) ≤ C := by
    intro g hg
    let zC : center S := ⟨zS, hzcenter⟩
    let a := centerCongr ((S : Subgroup G).normalizerMonoidHom ⟨g,hg⟩)
    have hz1 : zC ≠ 1 := by
      intro hh
      have hz : h.z = 1 := congrArg (fun w : center S => ((w : S) : G)) hh
      simpa [hz] using h.involution
    obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center S)).mp
      (ABG.QuasiDihedral.card_center (h.sylow_structure S).1)
    have haz1 : a zC ≠ 1 := fun hh => hz1 (a.injective (hh.trans a.map_one.symm))
    have heq : a zC = zC := (hw (a zC) haz1).trans (hw zC hz1).symm
    have hgfix : g * h.z * g⁻¹ = h.z :=
      congrArg (fun w : center S => ((w : S) : G)) heq
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgfix)
  have ht := S.normalizer_sup_eq_top' (hSC.trans hCN)
  rwa [sup_of_le_right (hNS.trans hCN)] at ht

/-- Simplicity is a consequence, not an extra hypothesis, of I.4.2. -/
public theorem isSimpleGroup (h : GL23InvolutionCentralizerHypotheses G) : IsSimpleGroup G := by
  have hz1 : h.z ≠ 1 := by intro hz; simpa [hz] using h.involution
  let : Nontrivial G := ⟨⟨h.z, 1, hz1⟩⟩
  refine ⟨fun N hN => ?_⟩
  let := hN
  by_cases heven : 2 ∣ Nat.card N
  · exact Or.inr (h.even_normal_eq_top N heven)
  · exact Or.inl (h.odd_normal_eq_bot N (Nat.not_even_iff_odd.mp (fun he => heven (even_iff_two_dvd.mp he))))

end CFSG.Quasithin.GL23InvolutionCentralizerHypotheses
