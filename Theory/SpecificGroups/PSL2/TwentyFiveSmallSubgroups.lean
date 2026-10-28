module

public import Theory.SpecificGroups.PSL2.TwentyFiveThirteen
public import GorensteinWalter.PSL2CoprimePrimeCentralizer
public import Theory.GroupTheory.SolvableOuterQuotient
import Mathlib.Tactic

/-!
# Small-index-two subgroup bounds over the twenty-five-element field

Dickson's classification bounds a PSL₂(25) subgroup whose order divides
forty by twenty. In an index-two extension this bounds subgroups whose
orders divide 20480 by forty. If every involution lies in the core, order
forty is impossible: its Sylow five-subgroup is normal, and its action
kernel has even order because Aut(C₅) has order four. The resulting core
involution centralizes an element of order five, contradicting the actual
PSL₂ defining-characteristic partition.

The literal mixed-extension consumer proves the involution condition from
its original semidihedral generators. Source: Aschbacher--Smith J.5.5(4),
printed p.447.
-/

public section

noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.PSL2.TwentyFive
variable {F : Type*} [Field F] [Finite F]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem five_power_le_one {m : ℕ} (h : 5^m∣40) : m≤1 := by
  by_contra hn
  have h2 : 2≤m := by omega
  have hd := dvd_trans (pow_dvd_pow 5 h2) h
  norm_num at hd

theorem card_le_twenty_of_dvd_forty (hF : Nat.card F=25)
    (H : Subgroup (PSL2MatrixGroup F)) (hdiv : Nat.card H∣40) : Nat.card H≤20 := by
  have hFp : Nat.card F=5^2 := hF
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFp H with
    hElem | hCyc | hDih | hA4 | hS4 | hA5 | hBorel | hPSL | hPGL
  · let : IsElementaryAbelian 5 H := hElem
    obtain ⟨m,hm⟩ := (IsElementaryAbelian.isPGroup 5 H).exists_card_eq
    rw [hm] at hdiv ⊢
    have hh := five_power_le_one hdiv
    interval_cases m <;> decide
  · obtain ⟨z,hz,hc,_⟩ := hCyc
    norm_num [hF] at hz
    rw [hc]
    rcases hz with hz|hz
    · exact (Nat.le_of_dvd (by decide : 0<12) hz).trans (by decide)
    · exact (Nat.le_of_dvd (by decide : 0<13) hz).trans (by decide)
  · obtain ⟨z,hz,hc,_⟩ := hDih
    norm_num [hF] at hz
    rw [hc] at hdiv ⊢
    rcases hz with hz|hz
    · have hd : 2*z∣24 := mul_dvd_mul_left 2 hz
      have hh := Nat.dvd_gcd hdiv hd
      norm_num at hh
      exact (Nat.le_of_dvd (by decide : 0<8) hh).trans (by decide)
    · have hd : 2*z∣26 := mul_dvd_mul_left 2 hz
      have hh := Nat.dvd_gcd hdiv hd
      norm_num at hh
      exact (Nat.le_of_dvd (by decide : 0<2) hh).trans (by decide)
  · obtain ⟨_,⟨e⟩⟩ := hA4
    have hc := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup,Nat.card_fin] at hc
    norm_num at hc
    omega
  · obtain ⟨_,⟨e⟩⟩ := hS4
    have hc := Nat.card_congr e.toEquiv
    rw [Nat.card_perm,Nat.card_fin] at hc
    norm_num at hc
    norm_num [hc] at hdiv
  · obtain ⟨_,⟨e⟩⟩ := hA5
    have hc := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup,Nat.card_fin] at hc
    norm_num at hc
    norm_num [hc] at hdiv
  · obtain ⟨m,t,_,ht,N,C,hN,_,hcN,_,hcC,hdisj,hsup⟩ := hBorel
    let : N.Normal := hN
    have hc : Nat.card H=5^m*t := by
      have hh := card_sup_eq_mul_of_normalizes_of_disjoint N C
        (by rw [N.normalizer_eq_top];exact le_top) hdisj
      simpa [hsup,hcN,hcC] using hh
    have hm := five_power_le_one (dvd_trans (hcN ▸ N.card_subgroup_dvd_card) hdiv)
    have ht40 : t∣40 := dvd_trans (hcC ▸ C.card_subgroup_dvd_card) hdiv
    norm_num at ht
    have ht4 : t∣4 := by simpa using Nat.dvd_gcd ht40 ht
    have htbound : t≤4 := Nat.le_of_dvd (by decide) ht4
    rw [hc]
    interval_cases m <;> simp only [pow_zero,pow_one,one_mul] <;> omega
  · obtain ⟨m,hm0,hmdiv,⟨e⟩⟩ := hPSL
    have hm : m=1 ∨ m=2 := (Nat.dvd_prime Nat.prime_two).mp hmdiv
    rcases hm with rfl|rfl
    · have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
        (F := GaloisField 5 1) (by rw [GaloisField.card 5 1 (by decide)];decide)
      rw [GaloisField.card 5 1 (by decide),←Nat.card_congr e.toEquiv] at hc
      norm_num at hc
      have h60 : Nat.card H=60 := by omega
      norm_num [h60] at hdiv
    · have hc := (Nat.card_congr e.toEquiv).trans (card (GaloisField.card 5 2 (by decide)))
      norm_num [hc] at hdiv
  · obtain ⟨m,hm0,hmdiv,⟨e⟩⟩ := hPGL
    have hmpos : 0<m := Nat.pos_of_ne_zero hm0
    have hbound := Nat.le_of_dvd (by decide : 0<2) hmdiv
    have hm : m=1 := by omega
    subst m
    have hc := GorensteinWalter.pgl2_card_formula (GaloisField 5 1)
    rw [GaloisField.card 5 1 (by decide),←Nat.card_congr e.toEquiv] at hc
    norm_num at hc
    norm_num [hc] at hdiv

namespace IndexTwo
variable {G : Type*} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal] (hN : N.index=2)
variable (e : N ≃* PSL2MatrixGroup F) (hF : Nat.card F=25)
include hN e hF

omit [Finite G] in
theorem card_le_forty_of_dvd (H : Subgroup G) (hdiv : Nat.card H∣20480) : Nat.card H≤40 := by
  let J : Subgroup N := H.subgroupOf N
  have hJH : Nat.card J∣Nat.card H := by
    change Nat.card (H.subgroupOf N)∣Nat.card H
    rw [←inf_subgroupOf_right H N,Nat.card_congr (subgroupOfEquivOfLe (show H⊓N≤N from inf_le_right)).toEquiv]
    exact card_dvd_of_le inf_le_left
  have hJN : Nat.card J∣7800 := by
    simpa only [Nat.card_congr e.toEquiv,card hF] using J.card_subgroup_dvd_card
  have hJ40 : Nat.card J∣40 := by
    simpa using Nat.dvd_gcd (dvd_trans hJH hdiv) hJN
  have hj := card_le_twenty_of_dvd_forty hF (J.map e.toMonoidHom)
    (by rwa [card_map_of_injective e.injective])
  rw [card_map_of_injective e.injective] at hj
  have hi := N.relIndex_dvd_index_of_normal H
  rw [hN,Nat.dvd_prime Nat.prime_two] at hi
  have hc := (N.subgroupOf H).card_mul_index
  have hswap : Nat.card (N.subgroupOf H)=Nat.card J := by
    change Nat.card (N.subgroupOf H)=Nat.card (H.subgroupOf N)
    rw [←inf_subgroupOf_right N H,←inf_subgroupOf_left H N]
    exact (Nat.card_congr (subgroupOfEquivOfLe (show N⊓H≤H from inf_le_right)).toEquiv).trans
      (Nat.card_congr (subgroupOfEquivOfLe (show N⊓H≤N from inf_le_left)).toEquiv).symm
  rw [hswap] at hc
  change Nat.card J*N.relIndex H=Nat.card H at hc
  rcases hi with hi|hi <;> rw [hi] at hc <;> omega

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem no_card_forty_of_involutions_in_core
    (hall : ∀x:G,x^2=1 → x∈N) (H : Subgroup G) (hH : Nat.card H=40) : False := by
  classical
  let P : Sylow 5 H := default
  have hp : Nat.card P=5 := by rw [P.card_eq_multiplicity,hH];decide +kernel
  have hi : P.index=8 := by
    have hc := P.toSubgroup.card_mul_index
    rw [hp,hH] at hc
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hmod := card_sylow_modEq_one 5 H
  have hc : Nat.card (Sylow 5 H)=1 := by
    obtain ⟨j,hj,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (Sylow 5 H)∣2^3 from hd)
    change Nat.card (Sylow 5 H)%5=1%5 at hmod
    interval_cases j <;> norm_num [he] at hmod
    simpa only [pow_zero] using he
  let : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hc).1
  let : P.Normal := P.normal_of_subsingleton
  let : Fact (Nat.Prime (Nat.card P)) := ⟨by rw [hp];decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hp
  let f : H →* MulAut P := MulAut.conjNormal
  have haut : Nat.card (MulAut P)=4 := by rw [IsCyclic.card_mulAut,hp];decide
  have hr : Nat.card f.range∣4 := haut ▸ f.range.card_subgroup_dvd_card
  have hprod : Nat.card f.ker*Nat.card f.range=40 := by
    simpa only [index_ker,hH] using f.ker.card_mul_index
  have hk : 2∣Nat.card f.ker := by
    obtain ⟨j,hj,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card f.range∣2^2 from hr)
    interval_cases j <;> simp only [he,Nat.reducePow,mul_one] at hprod <;> omega
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 hk
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hp])
  have hvG : orderOf ((v : H) : G)=2 := by simpa only [orderOf_coe] using hv
  have huG : orderOf ((u : H) : G)=5 := by simpa only [orderOf_coe] using hu
  have hvN : ((v : H) : G)∈N := hall _ (hvG ▸ pow_orderOf_eq_one _)
  have huN : ((u : H) : G)∈N := by
    have hPodd : Odd (Nat.card ((P : Subgroup H).map H.subtype)) := by
      rw [card_map_of_injective H.subtype_injective,hp]
      decide
    exact (GorensteinWalter.odd_card_subgroup_le_normal_index_two N
      ((P : Subgroup H).map H.subtype) inferInstance hN hPodd)
      (mem_map_of_mem H.subtype u.property)
  let uN : N := ⟨((u : H) : G),huN⟩
  let vN : N := ⟨((v : H) : G),hvN⟩
  have hcomm : Commute uN vN := by
    have hvC : (v : H)∈centralizer ((P : Subgroup H) : Set H) := by
      have hh := v.property
      change (v : H)∈(MulAut.conjNormal : H →* MulAut P).ker at hh
      simpa only [MulAut.conjNormal_ker_eq_centralizer] using hh
    apply Subtype.ext
    exact congrArg H.subtype (mem_centralizer_iff.mp hvC u u.property)
  exact GorensteinWalter.psl2_no_commuting_distinct_prime_order
    (show Nat.card F=5^2 from hF) (by decide : 2≠5)
    ((e.orderOf_eq uN).trans ((orderOf_coe uN).symm.trans huG))
    ((e.orderOf_eq vN).trans ((orderOf_coe vN).symm.trans hvG)) (hcomm.map e.toMonoidHom)

theorem card_le_twenty_of_involutions_in_core
    (hall : ∀x:G,x^2=1 → x∈N) (H : Subgroup G) (hdiv : Nat.card H∣20480) :
    Nat.card H≤20 := by
  have h40 := card_le_forty_of_dvd N hN e hF H hdiv
  have hd : Nat.card H∣80 := by
    have hc := H.card_subgroup_dvd_card
    rw [card_group N hN e hF] at hc
    simpa using Nat.dvd_gcd hdiv hc
  by_contra hn
  have hcard : Nat.card H=40 := by
    have hh : ∀n∈Finset.Icc (21 : ℕ) 40,n∣80 → n=40 := by decide +kernel
    exact hh _ (Finset.mem_Icc.mpr ⟨by omega,h40⟩) hd
  exact no_card_forty_of_involutions_in_core N hN e hF hall H hcard

end IndexTwo
end Theory.PSL2.TwentyFive
