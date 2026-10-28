module

public import Theory.GroupAction.PerfectCentralQuotient.ComponentImage
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.PerfectCentralCoverPrimeRank
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The surviving central involution in a component quotient

A central four-subgroup with a central involution maps to a line in the
containing component's central quotient. The original Sylow action fixes
that line. Its nonidentity element therefore has a full Sylow centralizer,
and the smaller quasisimple subgroup remains an ordinary fixed component.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeQuotient
universe u
variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
private theorem four_cases (V : Subgroup H) [IsKleinFour V]
    (v w : H) (hv : v ∈ V) (hw : w ∈ V)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v ≠ w) (x : H) (hx : x ∈ V) :
    x = 1 ∨ x = v ∨ x = w ∨ x = v * w := by
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  by_cases hxv : x = v
  · exact Or.inr (Or.inl hxv)
  by_cases hxw : x = w
  · exact Or.inr (Or.inr (Or.inl hxw))
  exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val
    (IsKleinFour.eq_mul_of_ne_all (x := (⟨v,hv⟩ : V)) (y := (⟨w,hw⟩ : V))
      (z := (⟨x,hx⟩ : V))
      (fun he => hv1 (congrArg Subtype.val he))
      (fun he => hw1 (congrArg Subtype.val he))
      (fun he => hvw (congrArg Subtype.val he))
      (fun he => hx1 (congrArg Subtype.val he))
      (fun he => hxv (congrArg Subtype.val he))
      (fun he => hxw (congrArg Subtype.val he))))))

/-- The literal central quotient contains the actual two-central fixed component. -/
theorem exists_fixed_component
    (B K V : Subgroup H) [IsQuasisimple B] [IsQuasisimple K] [K.Normal]
    [IsKleinFour V] (hBK : B ≤ K) (hZ : (center B).map B.subtype = V)
    (hCB : centralizer (V : Set H) ≤ normalizer (B : Set H))
    (T : Sylow 2 H) (hTB : (T : Subgroup H) ≤ normalizer (B : Set H))
    (v : H) (hv : v ∈ V) (hv1 : v ≠ 1) (hvZ : v ∈ center H)
    (hrank : 2 ≤ primeRank 3 B) (hcard : Nat.card (B ⧸ center B) = 20160)
    (hV : ¬ V ≤ (center K).map K.subtype) :
    ∃ t : K ⧸ center K, orderOf t = 2 ∧
      ∃ P : Sylow 2 (K ⧸ center K),
        (P : Subgroup (K ⧸ center K)) ≤ centralizer ({t} : Set (K ⧸ center K)) ∧
        ∃ D : Subgroup (centralizer ({t} : Set (K ⧸ center K))),
          IsComponent (centralizer ({t} : Set (K ⧸ center K))) D ∧
          20160 ∣ Nat.card D ∧ 2 ≤ primeRank 3 D := by
  have hVB : V ≤ B := hZ ▸ map_subtype_le _
  have hVK : V ≤ K := hVB.trans hBK
  obtain ⟨w, hw, hwZ⟩ := SetLike.not_le_iff_exists.mp hV
  let vk : K := ⟨v, hVK hv⟩
  let wk : K := ⟨w, hVK hw⟩
  have hvk : vk ∈ center K := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_center_iff.mp hvZ x)
  have hwk : wk ∉ center K := fun hz => hwZ (mem_map_of_mem K.subtype hz)
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hwZ (one_mem _)
  have hvw : v ≠ w := by
    intro he
    exact hwZ (he ▸ mem_map_of_mem K.subtype hvk)
  have hCw : centralizer ({w} : Set H) ≤ centralizer (V : Set H) := by
    intro x hx y hy
    rcases four_cases V v w hv hw hv1 hw1 hvw y hy with rfl | rfl | rfl | rfl
    · simp
    · exact (mem_center_iff.mp hvZ x).symm
    · exact (mem_centralizer_singleton_iff.mp hx).symm
    · have hvx := mem_center_iff.mp hvZ x
      have hwx := (mem_centralizer_singleton_iff.mp hx).symm
      calc
        v * w * x = v * (w * x) := mul_assoc _ _ _
        _ = v * (x * w) := by rw [hwx]
        _ = x * (v * w) := by rw [← mul_assoc, ← hvx, mul_assoc]
  let A := B.subgroupOf K
  let ea : A ≃* B := subgroupOfEquivOfLe hBK
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv ea.symm
  have hAC : A ≤ (MulAut.conj wk).fixedSubgroup := by
    intro a ha
    rw [MulAut.fixedSubgroup_conj]
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    obtain ⟨z,hz,he⟩ := mem_map.mp (hZ.symm ▸ hw)
    have hh := congrArg Subtype.val (mem_center_iff.mp hz (⟨a,ha⟩ : B))
    change (z : H) = w at he
    change (a : H) * (z : H) = (z : H) * (a : H) at hh
    rwa [he] at hh
  have hCA : (MulAut.conj wk).fixedSubgroup ≤ normalizer (A : Set K) := by
    intro x hx
    have hxH : (x : H) ∈ centralizer ({w} : Set H) := by
      rw [MulAut.fixedSubgroup_conj] at hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (hCB (hCw hxH)) a
  have hAcomp : IsComponentIn A (MulAut.conj wk).fixedSubgroup := by
    let : (A.subgroupOf (MulAut.conj wk).fixedSubgroup).Normal :=
      normal_subgroupOf_of_le_normalizer hCA
    let : IsQuasisimple (A.subgroupOf (MulAut.conj wk).fixedSubgroup) :=
      IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hAC).symm
    exact ⟨hAC, (inferInstance : (A.subgroupOf (MulAut.conj wk).fixedSubgroup).Normal).isSubnormal,
      inferInstance⟩
  let q := QuotientGroup.mk' (center K)
  let t := q wk
  have ht1 : t ≠ 1 := fun ht => hwk ((QuotientGroup.eq_one_iff wk).mp ht)
  have ht2 : t ^ 2 = 1 := by
    rw [← map_pow]
    have hw2 : wk ^ 2 = 1 := by
      apply Subtype.ext
      change w ^ 2 = 1
      simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using congrArg (fun x : V => (x : H))
        (IsKleinFour.mul_self (⟨w,hw⟩ : V))
    rw [hw2, map_one]
  have ht : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hqv : q vk = 1 := (QuotientGroup.eq_one_iff vk).mpr hvk
  obtain ⟨U,hU⟩ := T.exists_subgroupOf_eq_of_normal K
  let P := U.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hPC : (P : Subgroup (K ⧸ center K)) ≤ centralizer ({t} : Set (K ⧸ center K)) := by
    rintro _ ⟨x,hx,rfl⟩
    have hxT : (x : H) ∈ (T : Subgroup H) := by rw [hU] at hx; exact hx
    have hxV : (x : H) ∈ normalizer (V : Set H) := by
      rw [← hZ]
      exact (normalizer_le_normalizer_characteristic_image B (center B)) (hTB hxT)
    let y : K := x * wk * x⁻¹
    have hyV : (y : H) ∈ V := (mem_normalizer_iff.mp hxV w).mp hw
    have hy1 : (y : H) ≠ 1 := by
      intro he
      apply hw1
      exact (MulAut.conj (x : H)).injective (he.trans (map_one _).symm)
    have hyv : (y : H) ≠ v := by
      intro he
      apply hvw
      have hev : MulAut.conj (x : H) v = v := by
        change (x : H) * v * (x : H)⁻¹ = v
        rw [mem_center_iff.mp hvZ x, mul_inv_cancel_right]
      exact ((MulAut.conj (x : H)).injective (he.trans hev.symm)).symm
    have hyq : q y = q wk := by
      rcases four_cases V v w hv hw hv1 hw1 hvw y hyV with he | he | he | he
      · exact (hy1 he).elim
      · exact (hyv he).elim
      · exact congrArg q (Subtype.ext he)
      · have he' : y = vk * wk := Subtype.ext he
        rw [he', map_mul, hqv, one_mul]
    apply mem_centralizer_singleton_iff.mpr
    exact mul_inv_eq_iff_eq_mul.mp (by simpa only [y, map_mul, map_inv] using hyq)
  have heact : (center K).quotientAut (MulAut.conj wk) = MulAut.conj t := by
    ext z
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (center K) z
    rw [quotientAut_apply_mk]
    simp only [MulAut.conj_apply, map_mul, map_inv]
    rfl
  have hbar := MulAut.component_image_in_quotient_fixed (MulAut.conj wk) A hAcomp
  rw [heact, MulAut.fixedSubgroup_conj] at hbar
  let J := A.map q
  let C := centralizer ({t} : Set (K ⧸ center K))
  let D := J.subgroupOf C
  let ed : D ≃* J := subgroupOfEquivOfLe hbar.1
  let f := q.subgroupMap A
  let c : PerfectCentralCovering.Cover A J := {
    toMonoidHom := f
    surjective := q.subgroupMap_surjective A
    isPerfect := inferInstance
    ker_le_center := by
      intro a ha
      have haz : (a : K) ∈ center K :=
        (QuotientGroup.eq_one_iff (a : K)).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp ha))
      apply mem_center_iff.mpr
      intro b
      exact Subtype.ext (mem_center_iff.mp haz b) }
  have hqcard : Nat.card (J ⧸ center J) = 20160 := by
    rw [← Nat.card_congr c.quotientCenterEquiv.toEquiv]
    let ez := QuotientGroup.congr (center A) (center B) ea (by
      ext x
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact (MulEquivClass.apply_mem_center_iff ea).mpr ha
      · intro hx
        exact ⟨ea.symm x, (MulEquivClass.apply_mem_center_iff ea.symm).mpr hx,
          ea.apply_symm_apply x⟩)
    exact (Nat.card_congr ez.toEquiv).trans hcard
  have hJrank : 2 ≤ primeRank 3 J :=
    c.two_le_primeRank_target (by decide) (by rwa [primeRank_equiv 3 ea])
  refine ⟨t,ht,P,hPC,D,hbar.2,?_,?_⟩
  · rw [Nat.card_congr ed.toEquiv, ← hqcard]
    exact card_quotient_dvd_card (center J)
  · rwa [primeRank_equiv 3 ed]

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeQuotient
end
