module

public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.FirstCentralizer
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders
public import Theory.SpecificGroups.Tits.RelativeSylowMarking
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Five in the centralizer of a two-central Tits involution

An involution centralizing a full Sylow two-subgroup lies in that Sylow
subgroup. Sylow conjugacy and the certified order-two center identify its
conjugate with r5. The literal r5 centralizer has order 10240, divisible by
five. Both the involution and its full Sylow subgroup are retained.

Source: Parrott (1972), §5, p.683; Aschbacher–Smith 14.7.26, p.1053.
-/

public noncomputable section
open Subgroup
namespace Tits

theorem five_dvd_centralizer_of_sylow_fixed
    (t : Atlas1600Group) (ht : orderOf t = 2) (P : Sylow 2 Atlas1600Group)
    (hP : ∀ y ∈ P, Commute t y) :
    5 ∣ Nat.card (centralizer ({t} : Set Atlas1600Group)) := by
  have hpc : (P : Subgroup Atlas1600Group) ≤ centralizer (zpowers t : Set _) := by
    intro y hy a ha
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp ha
    exact ((hP y hy).zpow_left n).eq
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ht,pow_one])
  have hs := P.is_maximal' (P.isPGroup'.to_sup_of_normal_right' hp
    (hpc.trans (centralizer_le_normalizer _))) le_sup_left
  have htP : t ∈ P := (sup_eq_left.mp hs) (mem_zpowers t)
  obtain ⟨e,he⟩ := RelativeSylowMarking.exists_sylow_marking (MulEquiv.refl _) P
  have htne : t ≠ 1 := by intro h; simp [h] at ht
  have heroot : e t = atlas1600R5 :=
    RelativeSylowMarking.image_eq_r5_of_sylow_center e P he htP
      (fun y hy => (hP y hy).eq.symm) htne
  have hc := Nat.card_congr (MulAut.fixedSubgroupCongr e (MulAut.conj t)).toEquiv
  rw [MulAut.congr_conj,heroot,MulAut.fixedSubgroup_conj,
    MulAut.fixedSubgroup_conj,←RelativeParabolicNormalizers.first_eq_centralizer,
    ExceptionalParabolics.first_card] at hc
  rw [hc]
  norm_num

end Tits
