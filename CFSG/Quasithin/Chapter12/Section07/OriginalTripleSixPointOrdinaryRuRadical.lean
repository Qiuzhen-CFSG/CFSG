module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryRuCore
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Representatives
public import Theory.GroupTheory.PRadical.NormalizerRestriction
public import Theory.GroupAction.Defs

/-!
# The Rudvalis radical cannot centralize the original large image

When the radical normalizer fixes a central-class involution, radical
saturation puts the whole two-core of its centralizer in the radical.
An elementary subgroup of the radical center therefore meets that core
in at most two elements. Its image in the actual S5 quotient has order
dividing 120. The resulting order divides 240, excluding an elementary
subgroup of order at least 32.

Source: the Rudvalis inspection in Aschbacher--Smith C.3.1 and 12.7.5,
printed pp.151 and840. All cores and normalizers remain literal.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section07
open Subgroup Rudvalis

/-- Literal radical-normalizer control excludes the large original image. -/
theorem ordinary_ru_large_centered_radical_false
    (P E : Subgroup Model) (hP : P.IsPRadical 2) [IsElementaryAbelian 2 E]
    (hE : 32 ≤ Nat.card E) (hEP : E ≤ centerIn P)
    (z : Model) (hz : IsConj z (b^2))
    (hNC : normalizer (P : Set Model) ≤ centralizer ({z} : Set Model)) : False := by
  let C := centralizer ({z} : Set Model)
  let Q := C.pCoreIn 2
  have hQN : C ≤ normalizer (Q : Set Model) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hQP : Q ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P Q hP.isPGroup (isPGroup_pCoreIn 2 C) hP.2.le (hNC.trans hQN)
  have hEC : E ≤ C := (hEP.trans inf_le_left).trans (P.le_normalizer.trans hNC)
  let f : E →* C ⧸ pCore 2 C := (QuotientGroup.mk' (pCore 2 C)).comp (inclusion hEC)
  have hkQ (x : f.ker) : ((x.val : E) : Model) ∈ Q := by
    have hx : (inclusion hEC x.val : C) ∈ pCore 2 C :=
      (QuotientGroup.eq_one_iff _).mp x.property
    exact mem_map_of_mem C.subtype hx
  let j : f.ker → center Q := fun x =>
    ⟨⟨x.val,hkQ x⟩,mem_center_iff.mpr (fun q => Subtype.ext ((hEP x.val.property).2 q (hQP q.property)))⟩
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : center Q => (x.val : Model)) he
  have hk : Nat.card f.ker ≤ 2 :=
    (Nat.card_le_card_of_injective j hj).trans (ordinary_ru_point_core_center_card_le_two z hz)
  have hkpos : 0 < Nat.card f.ker := Nat.card_pos
  have hkd : Nat.card f.ker ∣ 2 := by
    interval_cases h : Nat.card f.ker <;> norm_num
  have hr : Nat.card f.range ∣ 120 := by
    have hd := card_subgroup_dvd_card f.range
    rw [Nat.card_congr (InvolutionCentralizers.firstQuotientEquiv hz).toEquiv,
      Nat.card_perm,Nat.card_fin] at hd
    norm_num at hd ⊢
    exact hd
  have hc : Nat.card E = Nat.card f.range * Nat.card f.ker := by
    rw [f.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hd : Nat.card E ∣ 240 := by
    rw [hc]
    exact Nat.mul_dvd_mul hr hkd
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hn5 : 5 ≤ n := by
    by_contra hh
    have hb : 2 ^ n < 2 ^ 5 := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [←hn] at hb
    norm_num at hb
    omega
  have h32 : 32 ∣ Nat.card E := by
    rw [hn]
    exact Nat.pow_dvd_pow 2 hn5
  exact (by decide : ¬ 32 ∣ 240) (h32.trans hd)

end CFSG.Quasithin.Chapter12.Section07
