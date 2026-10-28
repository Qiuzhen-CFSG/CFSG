module

public import Theory.GroupAction.QuaternionSixteenInvertedSection
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The center and exponent of an inverted cubic extension

An invariant proper central quotient of an order243 group would again
carry a fixed-point-free Q16 action, forcing it to have order at least81.
Thus, once the original normalizer quotient rules out an abelian D,
its center is exactly the cubic line W. A fixed cubic kernel and an
inverted elementary quotient force every cube to be trivial.

These are the final extraspecial-group deductions in Aschbacher,
Sporadic Groups (1994),45.8,printed p246.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem quaternion_inverted_section_center (S D W:Subgroup G) (e:S≃*QuaternionGroup 4) (z:G)
    (hzS:z∈S) (hz:orderOf z=2)
    (hSD:S≤normalizer (D:Set G)) (hSW:S≤normalizer (W:Set G))
    (hWD:W≤D) (hW:Nat.card W=3) (hcen:W≤centralizer (D:Set G))
    (hD:Nat.card D=243) (hne:¬D≤centralizer (D:Set G))
    (hi:∀d∈D,z*d*z⁻¹*d∈W) : (center D).map D.subtype=W := by
  let Z:Subgroup G:=(center D).map D.subtype
  have hZD:Z≤D:=map_subtype_le _
  have hWZ:W≤Z:=by
    intro w hw
    refine ⟨⟨w,hWD hw⟩,mem_center_iff.mpr ?_,rfl⟩
    intro d
    exact Subtype.ext (hcen hw d d.property)
  have hZZ:Z≤centralizer (Z:Set G):=by
    rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hx y)
  have hSZ:S≤normalizer (Z:Set G):=hSD.trans
    (normalizer_le_normalizer_characteristic_image D (center D))
  let : (W.subgroupOf Z).Normal:=(normal_subgroupOf_iff_le_normalizer hWZ).mpr
    ((le_centralizer_iff.mp (hWZ.trans hZZ)).trans (centralizer_le_normalizer _))
  by_contra hneZ
  have hn:(W.subgroupOf Z)≠⊤:=by
    intro ht
    have hh:=congrArg (fun A:Subgroup Z=>A.map Z.subtype) ht
    rw [map_subgroupOf_eq_of_le hWZ,←MonoidHom.range_eq_map,Z.range_subtype] at hh
    exact hneZ hh.symm
  let : Nontrivial (Z⧸W.subgroupOf Z):=QuotientGroup.nontrivial_iff.mpr hn
  have hp:IsPGroup 3 Z:=IsPGroup.of_card_dvd_pow (n:=5) (show Nat.card Z∣243 by simpa only [hD] using card_dvd_of_le hZD)
  obtain ⟨ρ,hρ⟩:=quaternion_sixteen_section_action S Z W e z hzS hz hSZ hSW (fun d hd=>hi d (hZD hd))
  have hq:=Theory.GroupAction.QuaternionSixteenTernaryDegree.card_ge_eighty_one_of_inversion
    (hp.to_quotient (W.subgroupOf Z)) ρ hρ
  have hmul:=card_eq_card_quotient_mul_card_subgroup (W.subgroupOf Z)
  rw [Nat.card_congr (subgroupOfEquivOfLe hWZ).toEquiv,hW] at hmul
  have hZD':Z=D:=eq_of_le_of_card_ge hZD (by rw [hD];omega)
  apply hne
  intro d hd x hx
  have hdZ:d∈Z:=hZD'.symm ▸ hd
  obtain ⟨d,hdc,rfl⟩:=hdZ
  exact congrArg Subtype.val (mem_center_iff.mp hdc ⟨x,hx⟩)
end Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
omit [Finite G] in
theorem nonabelian_of_odd_centralizer_quotient (D V F:Subgroup G)
    (hD:Nat.card D=243) (hFV:V≤centralizer (F:Set G)) (hFD:F≤D)
    (hVN:normalizer (F:Set G)≤normalizer (V:Set G))
    (hindex:V.relIndex (normalizer (F:Set G))=24)
    (hcap:Nat.card (D⊓V:Subgroup G)=27) : ¬D≤centralizer (D:Set G) := by
  intro habel
  let N:=normalizer (F:Set G)
  have hDN:D≤N:=(habel.trans (centralizer_le hFD)).trans (centralizer_le_normalizer _)
  have hVN':V≤N:=hFV.trans (centralizer_le_normalizer _)
  let : (V.subgroupOf N).Normal:=(normal_subgroupOf_iff_le_normalizer hVN').mpr hVN
  have hd:=relIndex_dvd_index_of_normal (V.subgroupOf N) (D.subgroupOf N)
  rw [relIndex_subgroupOf hDN] at hd
  change V.relIndex D∣V.relIndex N at hd
  rw [hindex] at hd
  have hh:=relIndex_mul_relIndex (⊥:Subgroup G) (D⊓V) D bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hcap,hD] at hh
  have he:V.relIndex D=9:=by omega
  rw [he] at hd
  norm_num at hd
end Subgroup
namespace MulAut
variable {A:Type*} [Group A]
theorem exponent_three_of_fixed_cubic_inverted_quotient (C:Subgroup A) [C.Normal]
    (hC:Nat.card C=3) (hcen:C≤Subgroup.center A)
    (a:MulAut A) (hf:∀c∈C,a c=c) (hi:∀x,a x*x∈C)
    [IsElementaryAbelian 3 (A⧸C)] : ∀x:A,x^3=1 := by
  intro x
  have hx3:x^3∈C:=by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' C (x^3)=1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 (A⧸C)) _
  have hwp:(a x*x)^3=1:=by
    have hh:=pow_card_eq_one' (x:=(⟨a x*x,hi x⟩:C))
    rw [hC] at hh
    exact congrArg Subtype.val hh
  have hc:Commute (a x) x:=by
    have hh:=Subgroup.mem_center_iff.mp (hcen (hi x)) x
    exact mul_right_cancel (by simpa only [mul_assoc] using hh.symm)
  rw [hc.mul_pow,←map_pow,hf _ hx3] at hwp
  let y:C:=⟨x^3,hx3⟩
  have hy2:y^2=1:=by
    apply Subtype.ext
    exact pow_two (x^3) |>.trans hwp
  have hy:y=1:=orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide:Nat.Coprime 3 2)
    (hC ▸ orderOf_dvd_natCard y) (orderOf_dvd_of_pow_eq_one hy2))
  exact congrArg Subtype.val hy
end MulAut
