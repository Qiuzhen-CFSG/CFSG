module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Local
public import Theory.GroupTheory.Recognition.QuasithinM23.CentralInvolution
public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# The original central involution, its ambient centralizer, and the TI core

For the exceptional overcomponent J in the nonmaximal linear row, the actual
faithful A₇ action on U = O₂(J) identifies Z(T) as a line and makes J transitive
on U minus the identity. The point-stabilizer calculation gives O₂(C_J(z)) = U.
Since C_J(z) contains the original Sylow subgroup T, O₂(C_G(z)) lies in U.
The abelian group U centralizes that core, so characteristic two forces the
reverse inclusion. Hence C_G(z) normalizes U and lies in J = N_G(U).

Transport of the same centralizer quotient gives PSL₃(2). Transitivity then
puts the centralizer of every nonidentity element of U in J, and the actual
I.6.1(1) criterion proves U is TI in G. The order-two Sylow center also gives
N_G(T) ≤ C_G(z), the containment used in source 5.2.21.

This proves 5.2.12(1),(3),(4), the centralizer equality and core/quotient part of
(2). The full natural-block marking of (2) and ambient M₂₃ recognition remain
separate obligations. Source: Aschbacher–Smith 5.2.12, printed p.654, and 5.2.21,
printed p.657 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- Original ambient centralizer control from the prepared nonmaximal linear
row, retaining the actual exceptional core, Sylow group, and quotient. -/
theorem Preparation.linear_exceptional_centralizer_geometry
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : residual H < J) :
    Nat.card (center T) = 2 ∧
      (∀ x y : G, x ∈ J.pCoreIn 2 → y ∈ J.pCoreIn 2 → x ≠ 1 → y ≠ 1 →
        ∃ a : J, (a : G)*x*(a : G)⁻¹ = y) ∧
      ∃ z : G, z ∈ J.pCoreIn 2 ∧ orderOf z = 2 ∧
        (center T).map (T : Subgroup G).subtype = zpowers z ∧
        centralizer ({z} : Set G) ≤ J ∧
        (centralizer ({z} : Set G)).pCoreIn 2 = J.pCoreIn 2 ∧
        Nonempty ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        ChapterI.Section06To08.IsTISubgroup (J.pCoreIn 2) ∧
        normalizer ((T : Subgroup G) : Set G) ≤ centralizer ({z} : Set G) := by
  have hTH := hH.1.1.2
  have hn := (d.block_overcomponent_parameter h hTH hp F hm hF (.inl he) hJ.1 hKJ).1
  have hb := d.linear_four_overcomponent_exceptional (hn ▸ h) hTH hp F hm hF he hJ.1 hKJ
  obtain ⟨ha,hcard,_⟩ := d.linear_overcomponent_action h hTH hp F hm hF he hJ.1 hKJ.le
  rw [hn] at hcard
  have hcard : Nat.card (pCore 2 J) = 16 := hcard
  let := ha
  let : IsElementaryAbelian 2 (J.pCoreIn 2) := ha.map J.subtype
  obtain ⟨hTJ,hHJ,hmax,hNJ,hNU,hCU,hcoreH,hcardJ⟩ :=
    d.linear_exceptional_local h hH hp F hm hF he hJ hKJ
  have hCU0 : centralizer (pCore 2 J : Set J) = pCore 2 J :=
    le_antisymm
      (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
        (h.qtke.evenCharacteristic T) hJ.1)
      (fun x hx y hy => setLike_mul_comm hy hx)
  let e := hb.2.1.some
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = centralizer (pCore 2 J : Set J) := by
    rw [hCU0]
    exact (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans
      (QuotientGroup.ker_mk' _)
  have htrans (x y : G) (hx : x ∈ J.pCoreIn 2) (hy : y ∈ J.pCoreIn 2)
      (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ a : J, (a : G)*x*(a : G)⁻¹ = y := by
    obtain ⟨x,hx,rfl⟩ := hx
    obtain ⟨y,hy,rfl⟩ := hy
    obtain ⟨a,ha⟩ := QuasithinM23.core_transitive (pCore 2 J) hcard q hq hk hx hy
      (fun hh => hx1 (congrArg Subtype.val hh)) (fun hh => hy1 (congrArg Subtype.val hh))
    exact ⟨a,congrArg Subtype.val ha⟩
  obtain ⟨hCP,hZP⟩ := QuasithinM23.sylow_center_two (pCore 2 J) hcard q hq hk hCU0 (T.subtype hTJ)
  have hZT : Nat.card (center T) = 2 :=
    (Nat.card_congr (centerCongr (subgroupOfEquivOfLe hTJ)).toEquiv).symm.trans hZP
  obtain ⟨z0,hz0,hunique⟩ := (Nat.card_eq_two_iff' (1 : center T)).mp hZT
  let z : G := z0.val.val
  have hz1 : z ≠ 1 := fun he => hz0 (Subtype.ext (Subtype.ext he))
  have hzT : z ∈ (T : Subgroup G) := z0.val.property
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp z0.property ⟨t,ht⟩))
  have hzU : z ∈ J.pCoreIn 2 := by
    refine mem_map.mpr ⟨⟨z,hTJ hzT⟩,?_,rfl⟩
    apply hCP
    intro t ht
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hTC ht)
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hzU) hz1
  have hZeq : (center T).map (T : Subgroup G).subtype = zpowers z := by
    apply le_antisymm
    · rintro x ⟨t,ht,rfl⟩
      change (t : G) ∈ zpowers z
      by_cases ht1 : (⟨t,ht⟩ : center T) = 1
      · have he : (t : G) = 1 := congrArg (fun u : center T => (u.val : G)) ht1
        rw [he]; exact one_mem _
      · have he := hunique ⟨t,ht⟩ ht1
        have he' : (t : G) = z := congrArg (fun u : center T => (u.val : G)) he
        rw [he']; exact mem_zpowers z
    · exact zpowers_le.mpr (mem_map_of_mem _ z0.property)
  let zJ : J := ⟨z,hTJ hzT⟩
  have hzJ : zJ ∈ pCore 2 J := (mem_map_iff_mem J.subtype_injective).mp hzU
  have hzJ1 : zJ ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  obtain ⟨hlocal,hquot⟩ :=
    QuasithinM23.point_centralizer_geometry (pCore 2 J) hcard q hq hk hCU0 hzJ hzJ1
  let C := centralizer ({z} : Set G)
  let Y := J ⊓ C
  have hY : (centralizer ({zJ} : Set J)).map J.subtype = Y :=
    map_subtype_centralizer_singleton J zJ
  have hcoreY : Y.pCoreIn 2 = J.pCoreIn 2 := by
    rw [←hY,←map_pCoreIn_of_injective 2 _ J.subtype J.subtype_injective,hlocal]
    rfl
  have hTY : (T : Subgroup G) ≤ Y := le_inf hTJ hTC
  have hchar : C ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T)
      ⟨Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer hz2),hTC⟩
  have hQU : C.pCoreIn 2 ≤ J.pCoreIn 2 :=
    (Chapter3.twoCore_le_of_sylow_le T hTY inf_le_right).trans_eq hcoreY
  have hUC : J.pCoreIn 2 ≤ C := by
    intro u hu
    exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hu hzU)
  have hcoreC : C.pCoreIn 2 = J.pCoreIn 2 := by
    apply le_antisymm hQU
    intro u hu
    exact hchar ⟨hUC hu,fun v hv => setLike_mul_comm (hQU hv) hu⟩
  have hCJ : C ≤ J := by
    rw [←hNU,←hcoreC]
    exact C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hYC : Y = C := inf_eq_right.mpr hCJ
  let a : (centralizer ({zJ} : Set J)) ≃* C :=
    ((centralizer ({zJ} : Set J)).equivMapOfInjective J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr (hY.trans hYC))
  have hquotC : Nonempty (C ⧸ pCore 2 C ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans hquot.some⟩
  have hcentral (x : G) (hx : x ∈ J.pCoreIn 2) (hx1 : x ≠ 1) :
      centralizer ({x} : Set G) ≤ J := by
    obtain ⟨a,ha⟩ := htrans x z hx hzU hx1 hz1
    intro c hc
    have hac : (a : G)*c*(a : G)⁻¹ ∈ C := by
      apply mem_centralizer_singleton_iff.mpr
      rw [←ha]
      calc
        ((a : G)*c*(a : G)⁻¹)*((a : G)*x*(a : G)⁻¹) =
          (a : G)*(c*x)*(a : G)⁻¹ := by group
        _ = (a : G)*(x*c)*(a : G)⁻¹ := by rw [mem_centralizer_singleton_iff.mp hc]
        _ = ((a : G)*x*(a : G)⁻¹)*((a : G)*c*(a : G)⁻¹) := by group
    have hh := J.mul_mem (J.mul_mem (J.inv_mem a.property) (hCJ hac)) a.property
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel_right,inv_mul_cancel,mul_one] using hh
  have hTI : ChapterI.Section06To08.IsTISubgroup (J.pCoreIn 2) := by
    apply ChapterI.Section06To08.lemma_I_6_1_1 (J.pCoreIn 2) J hNU.symm hcentral
    intro x y hx hy ⟨a,ha⟩
    by_cases hx1 : x = 1
    · subst x
      have hy1 : y = 1 := by simpa using ha.symm
      subst y
      exact ⟨1,by simp⟩
    · have hy1 : y ≠ 1 := by
        intro he
        apply hx1
        have hh : (MulAut.conj a) x = 1 := ha.trans he
        exact (MulAut.conj a).injective (hh.trans (map_one _).symm)
      exact htrans x y hx hy hx1 hy1
  have hNT : normalizer ((T : Subgroup G) : Set G) ≤ centralizer ({z} : Set G) := by
    rw [←normalizer_zpowers_eq_centralizer_of_order_two z hz2,←hZeq]
    exact normalizer_le_normalizer_characteristic_image (T : Subgroup G) (center T)
  exact ⟨hZT,htrans,z,hzU,hz2,hZeq,hCJ,hcoreC,hquotC,hTI,hNT⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
