module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverSeparation
public import Theory.SpecificGroups.Janko1.Model.SylowTwo
public import Theory.ElementaryAbelian.Injective
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.GroupTheory.Perm.Cycle.Type
/-!
# Small containing models excluded by the central two-cover

SL2(5) cannot embed in A7: its central involution would place all 120
elements in a permutation centralizer of order 48. An explicit order-four
matrix excludes J1, whose Sylow two-subgroups are elementary abelian.
A solvable odd-order kernel intersects the center of SL2(5) trivially,
so the A7 obstruction also excludes its actual central three-cover.
Source: the restricted A.3.12 list in Aschbacher–Smith C.5.12, p.163.
-/
public section
open Subgroup Theory.GroupTheory Equiv
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels
variable {B : Type*} [Group B] [Finite B]
private theorem seven_involution_centralizer_card (t : alternatingGroup (Fin 7))
    (ht : orderOf t=2) : Nat.card (centralizer ({(t : Perm (Fin 7))} : Set (Perm (Fin 7))))=48 := by
  have ho : orderOf (t : Perm (Fin 7)) = 2 := (Subgroup.orderOf_coe t).trans ht
  obtain ⟨k,hk⟩ := Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := (t : Perm (Fin 7)).sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at hbound
  have hs := Perm.mem_alternatingGroup.mp t.property
  rw [Perm.sign_of_cycleType',hk] at hs
  have hkb : k ≤ 2 := by omega
  have hk1 : k=1 := by
    interval_cases k
    · norm_num at hs
    · rfl
    · norm_num at hs
  have hc : (t : Perm (Fin 7)).cycleType={2,2} := by simpa [hk1] using hk
  rw [Perm.nat_card_centralizer,hc]
  norm_num

theorem no_sl2_five_injective_alternating_seven (hB : IsSL B 2 5)
    (f : B →* alternatingGroup (Fin 7)) (hf : Function.Injective f) : False := by
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center B) 2
    (by rw [sl2_five_center_card hB])
  let t := f z
  have ht : orderOf t=2 := (orderOf_injective f hf z).trans ((Subgroup.orderOf_coe z).trans hz)
  let j : B →* centralizer ({(t : Perm (Fin 7))} : Set (Perm (Fin 7))) :=
    ((alternatingGroup (Fin 7)).subtype.comp f).codRestrict _ (by
      intro b
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg (fun x : alternatingGroup (Fin 7) => (x : Perm (Fin 7)))
        (by simpa only [map_mul] using congrArg f (mem_center_iff.mp z.property b)))
  have hj : Function.Injective j := by
    intro a b hab
    apply hf
    apply Subtype.ext
    exact congrArg (fun x : centralizer ({(t : Perm (Fin 7))} : Set (Perm (Fin 7))) => (x : Perm (Fin 7))) hab
  have hd := card_dvd_of_injective j hj
  rw [sl2_five_card hB,seven_involution_centralizer_card t ht] at hd
  norm_num at hd

private def sl25_four : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
  ⟨!![0,-1;1,0],by decide⟩
private theorem sl25_four_pow : sl25_four^4=1 := by decide +kernel
private theorem sl25_four_square : sl25_four^2≠1 := by decide +kernel

omit [Finite B] in
theorem no_sl2_five_injective_janko_one (hB : IsSL B 2 5)
    (f : B →* Janko1.Model) (hf : Function.Injective f) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hB
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (K := F) (K' := ZMod 5) (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let eB := e.trans (Atlas.fieldEquivSL 2 eF)
  let g := f.comp eB.symm.toMonoidHom
  have hg : Function.Injective g := hf.comp eB.symm.injective
  have hp : IsPGroup 2 (zpowers (g sl25_four)) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    change (g sl25_four)^4=1
    rw [← map_pow,sl25_four_pow,map_one]
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  let : IsElementaryAbelian 2 S := Janko1.SylowTwo.elementary S
  have hm : g sl25_four ∈ (S : Subgroup Janko1.Model) := hS (mem_zpowers _)
  have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) (g sl25_four) hm
  apply sl25_four_square
  apply hg
  exact (map_pow g sl25_four 2).trans (hs.trans (map_one g).symm)

/-- Odd-order solvable kernels cannot kill any part of the central two-cover. -/
theorem sl2_five_injective_of_odd_solvable_kernel [IsQuasisimple B]
    (hB : IsSL B 2 5) {H : Type*} [Group H]
    (f : B →* H) [Group.IsSolvable f.ker] (ho : Odd (Nat.card f.ker)) :
    Function.Injective f := by
  have hkc : f.ker ≤ center B := (le_solvableRadical f.ker inferInstance inferInstance).trans
    IsQuasisimple.solvableRadical_le_center
  have hd : Nat.card f.ker ∣ 2 := by
    rw [← sl2_five_center_card hB]
    exact card_dvd_of_le hkc
  have hc : Nat.card f.ker=1 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right
    (fun h => by rw [h] at ho; norm_num at ho)
  exact (MonoidHom.ker_eq_bot_iff f).mp (Subgroup.card_eq_one.mp hc)

theorem no_sl2_five_injective_three_alternating_seven [IsQuasisimple B]
    (hB : IsSL B 2 5) {H : Type*} [Group H] [Finite H]
    (hH : IsAlternatingCover H 7) (f : B →* H) (hf : Function.Injective f) : False := by
  obtain ⟨_,⟨ec⟩,⟨eq⟩⟩ := hH
  let q := QuotientGroup.mk' (center H)
  let g := q.comp f
  let k : g.ker →* center H := (f.comp g.ker.subtype).codRestrict _
    (fun x => (QuotientGroup.eq_one_iff _).mp x.property)
  have hk : Function.Injective k := by
    intro x y he
    exact Subtype.ext (hf (congrArg Subtype.val he))
  let : Group.IsSolvable (center H) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  let : Group.IsSolvable g.ker := Group.isSolvable_of_isSolvable_injective (f := k) hk
  have ho : Odd (Nat.card g.ker) := by
    have hc : Nat.card (center H)=3 := by rw [Nat.card_congr ec.toEquiv]; simp
    exact (show Odd (Nat.card (center H)) by rw [hc]; decide).of_dvd_nat (card_dvd_of_injective k hk)
  have hg := sl2_five_injective_of_odd_solvable_kernel hB g ho
  exact no_sl2_five_injective_alternating_seven hB (eq.toMonoidHom.comp g) (eq.injective.comp hg)

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
