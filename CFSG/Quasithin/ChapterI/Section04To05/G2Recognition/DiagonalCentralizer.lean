module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PairedCoreCentralizer
public import Theory.GroupTheory.CentralCoprimeCardLift
public import Theory.GroupTheory.CyclicSylowTwoComplement

/-!
# Diagonal cubic centralizers and the common-line odd core

A cubic with nonidentity components in both marked SL₂(3) factors has
centralizer in H of order dividing18. Centralizing its product forces
centralization of each component: the possible error lies in the common
central two-group, where its order also divides three. Thus a cubic in H
whose centralizer order is divisible by four must be conjugate to a factor
line.

In the order27-core branch, K=D∩E is conjugate to neither factor line.
A central involution in a Sylow two-subgroup of C_G(K), transported into
H by the proved involution fusion, now forces that Sylow subgroup to
have order two. Burnside transfer gives the literal odd core of C_G(K)
index two. It has order divisible by 3^5 by `PairedCoreCentralizer`.

The original torus normalizes K and hence this odd core. Each torus
involution has odd fixed subgroup of order dividing nine. The
Brauer–Wielandt formula bounds the odd-core order by 3^6, leaving exactly
243 or729, and C_G(K) has order486 or1458.

Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417. This continues the
exceptional q=3 analysis using the actual marked factors and torus, the
ordinary centralizer and its literal odd core. These two remaining
centralizer orders are not excluded here. The order27-core exclusion,
Sylow-nine branch and Atlas recognition remain open.
`Chapter14DiagonalCentralizer` supplies the original SourceLocalData
application without any new centralizer or odd-core hypothesis.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal

omit [Finite G] in
private theorem fix_factor_of_fix_product (a : c.H₁) (ha : a^3=1)
    (b : c.H₂) (h : c.H)
    (hfix : h*((a:c.H)*(b:c.H))*h⁻¹=(a:c.H)*(b:c.H)) :
    h*(a:c.H)*h⁻¹=(a:c.H) := by
  let q := QuotientGroup.mk' c.H₂
  let f : c.H₁ →* c.H ⧸ c.H₂ := q.comp c.H₁.subtype
  have hker (a : c.H₁) : a∈f.ker ↔ (a:c.H)∈c.H₂ := QuotientGroup.eq_one_iff _
  have hcenter : f.ker ≤ center c.H₁ := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (c.commute y y.property x ((hker x).mp hx))
  have hmap : f.ker.map c.H₁.subtype=c.H₁⊓c.H₂ := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,(hker a).mp ha⟩
    · rintro ⟨ha,hb⟩
      exact ⟨⟨x,ha⟩,(hker ⟨x,ha⟩).mpr hb,rfl⟩
  have hcard : Nat.card f.ker=2 := by
    rw [←card_map_of_injective c.H₁.subtype_injective,hmap,intersection_card c]
  let a' : c.H₁ := MulAut.conjNormal h a
  have hb : q (b:c.H)=1 := (QuotientGroup.eq_one_iff _).mpr b.property
  have he : f a'=f a := by
    change q (h*(a:c.H)*h⁻¹)=q (a:c.H)
    simpa only [map_mul,map_inv,hb,mul_one] using congrArg q hfix
  have ha' : a'^3=1 := by
    change (MulAut.conjNormal h a)^3=1
    rw [←map_pow,ha,map_one]
  exact congrArg Subtype.val
    (f.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker hcenter
      (by rw [hcard]; decide : (Nat.card f.ker).Coprime 3) he ha' ha)

private theorem sl23_cubic_centralizer_card {J : Type*} [Group J] [Finite J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) (b : J) (hb : orderOf b=3) :
    Nat.card (Subgroup.centralizer ({b}:Set J))=6 := by
  have he : (Subgroup.centralizer ({b}:Set J)).map e.toMonoidHom =
      Subgroup.centralizer ({e b}:Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      change e x*e b=e b*e x
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hx)
    · intro x hx
      refine ⟨e.symm x,mem_centralizer_singleton_iff.mpr ?_,e.apply_symm_apply x⟩
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx
  rw [←card_map_of_injective (f:=e.toMonoidHom) e.injective,he]
  exact Matrix.SpecialLinearGroup.cubic_centralizer_card (e b) ((e.orderOf_eq b).trans hb)

theorem factor_product_local_centralizer_card_dvd (a : c.H₁) (b : c.H₂)
    (ha : orderOf a=3) (hb : orderOf b=3) :
    Nat.card (Subgroup.centralizer ({(a:c.H)*(b:c.H)}:Set c.H)) ∣ 18 := by
  let Q := (Subgroup.centralizer ({b}:Set c.H₂)).map c.H₂.subtype
  let X := zpowers (a:c.H)
  have hX₁ : X ≤ c.H₁ := zpowers_le.mpr a.property
  have hQ₂ : Q ≤ c.H₂ := map_subtype_le _
  have hXC : X ≤ Subgroup.centralizer (Q:Set c.H) := by
    intro x hx q hq
    exact (c.commute x (hX₁ hx) q (hQ₂ hq)).symm
  have hQ : Nat.card Q=6 := by
    rw [card_map_of_injective c.H₂.subtype_injective]
    exact sl23_cubic_centralizer_card c.H₂_model.some b hb
  have hX : Nat.card X=3 := by rw [Nat.card_zpowers,orderOf_coe,ha]
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q X
    (hXC.trans (Subgroup.centralizer_le_normalizer _))
  rw [hQ,hX] at hprod
  have hd : Nat.card (Q⊔X:Subgroup c.H) ∣ 18 :=
    ⟨Nat.card (Q⊓X:Subgroup c.H),by nlinarith [hprod]⟩
  apply (card_dvd_of_le (show Subgroup.centralizer ({(a:c.H)*(b:c.H)}:Set c.H)≤Q⊔X from ?_)).trans hd
  intro h hh
  have hfix : h*((a:c.H)*(b:c.H))*h⁻¹=(a:c.H)*(b:c.H) :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hh)
  have hfa : h*(a:c.H)*h⁻¹=(a:c.H) := fix_factor_of_fix_product c a
    (ha ▸ pow_orderOf_eq_one a) b h hfix
  have hfb : h*(b:c.H)*h⁻¹=(b:c.H) := by
    apply mul_left_cancel (a:=(a:c.H))
    calc
      _ = (h*(a:c.H)*h⁻¹)*(h*(b:c.H)*h⁻¹) := by rw [hfa]
      _ = h*((a:c.H)*(b:c.H))*h⁻¹ := by group
      _ = _ := hfix
  have hC : h∈Subgroup.centralizer ({(a:c.H)}:Set c.H) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfa)
  rw [left_cubic_local_centralizer c a ha] at hC
  change h∈(↑(c.H₂⊔X):Set c.H) at hC
  rw [coe_mul_of_right_le_normalizer_left c.H₂ X (le_normalizer_of_normal)] at hC
  obtain ⟨u,hu,v,hv,huv⟩ := hC
  have hvb : v*(b:c.H)=(b:c.H)*v := c.commute v (hX₁ hv) b b.property
  have hub : u*(b:c.H)=(b:c.H)*u := by
    have hh := mul_inv_eq_iff_eq_mul.mp hfb
    rw [←huv,mul_assoc,hvb,←mul_assoc,←mul_assoc] at hh
    exact mul_right_cancel hh
  have huQ : u∈Q := ⟨⟨u,hu⟩,mem_centralizer_singleton_iff.mpr (Subtype.ext hub),rfl⟩
  exact huv ▸ (Q⊔X).mul_mem (mem_sup_left huQ) (mem_sup_right hv)

namespace CubicTorus
variable {c}

theorem diagonal_local_centralizer_card_dvd (t : CubicTorus c) (u : c.H)
    (hu : u ∈ zpowers (t.x:c.H) ⊔ zpowers (t.y:c.H))
    (hx : u ∉ zpowers (t.x:c.H)) (hy : u ∉ zpowers (t.y:c.H)) :
    Nat.card (Subgroup.centralizer ({u}:Set c.H)) ∣ 18 := by
  let X := zpowers (t.x:c.H)
  let Y := zpowers (t.y:c.H)
  have hX₁ : X≤c.H₁ := zpowers_le.mpr t.x.property
  have hY₂ : Y≤c.H₂ := zpowers_le.mpr t.y.property
  have hn : Y ≤ normalizer (X:Set c.H) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy x hx
    exact c.commute x (hX₁ hx) y (hY₂ hy)
  change u∈(↑(X⊔Y):Set c.H) at hu
  rw [coe_mul_of_right_le_normalizer_left X Y hn] at hu
  obtain ⟨a,ha,b,hb,hab⟩ := hu
  change a*b=u at hab
  have ha1 : a≠1 := by intro he; apply hy; rw [←hab,he,one_mul]; exact hb
  have hb1 : b≠1 := by intro he; apply hx; rw [←hab,he,mul_one]; exact ha
  have ha3 : orderOf a=3 := by
    have hd := orderOf_dvd_of_mem_zpowers ha
    rw [orderOf_coe,t.x_order] at hd
    exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
      (fun h => ha1 (orderOf_eq_one_iff.mp h))
  have hb3 : orderOf b=3 := by
    have hd := orderOf_dvd_of_mem_zpowers hb
    rw [orderOf_coe,t.y_order] at hd
    exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
      (fun h => hb1 (orderOf_eq_one_iff.mp h))
  rw [←hab]
  exact factor_product_local_centralizer_card_dvd c ⟨a,hX₁ ha⟩ ⟨b,hY₂ hb⟩
    ((orderOf_coe _).symm.trans ha3) ((orderOf_coe _).symm.trans hb3)

theorem local_cubic_four_dvd_forces_factor (t : CubicTorus c) (u : c.H)
    (hu : orderOf u=3) (hfour : 4∣Nat.card (Subgroup.centralizer ({u}:Set c.H))) :
    ∃ g : G,
      (zpowers (u:G)).map (MulAut.conj g).toMonoidHom=zpowers ((t.x:c.H):G) ∨
      (zpowers (u:G)).map (MulAut.conj g).toMonoidHom=zpowers ((t.y:c.H):G) := by
  let B : Subgroup c.H := zpowers (t.x:c.H) ⊔ zpowers (t.y:c.H)
  have hmap : B.map c.H.subtype=zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  have hB : Nat.card B=9 := by
    rw [←card_map_of_injective c.H.subtype_injective,hmap]
    exact (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  have hi : B.index=64 := by
    have hh := B.card_mul_index
    rw [hB,H_card c] at hh
    omega
  let P : Sylow 3 c.H := (IsPGroup.of_card (p:=3) (n:=2) hB).toSylow
    (by rw [hi]; decide)
  obtain ⟨b,hb⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n:=1) (by simpa using hu)
  obtain ⟨h,hh⟩ := isConj_iff.mp hb
  have hb3 : orderOf (b:c.H)=3 := by
    calc
      _ = orderOf (MulAut.conj h u) := congrArg orderOf hh.symm
      _ = 3 := ((MulAut.conj h).orderOf_eq u).trans hu
  have hb4 : 4∣Nat.card (Subgroup.centralizer ({(b:c.H)}:Set c.H)) := by
    rwa [←card_centralizer_eq_of_isConj u (b:c.H) hb]
  have hcases : (b:c.H)∈zpowers (t.x:c.H) ∨ (b:c.H)∈zpowers (t.y:c.H) := by
    by_contra he
    push Not at he
    have hd := t.diagonal_local_centralizer_card_dvd b b.property he.1 he.2
    have hh := hb4.trans hd
    norm_num at hh
  have hgen {a : c.H} (ha : orderOf a=3) (hm : (b:c.H)∈zpowers a) :
      (zpowers (u:G)).map (MulAut.conj (h:G)).toMonoidHom=zpowers (a:G) := by
    have heq : zpowers (b:c.H)=zpowers a := eq_of_le_of_card_ge (zpowers_le.mpr hm)
      (by rw [Nat.card_zpowers,Nat.card_zpowers,hb3,ha])
    have he := congrArg (fun A : Subgroup c.H => A.map c.H.subtype) heq
    rw [MonoidHom.map_zpowers,MonoidHom.map_zpowers] at he
    rw [MonoidHom.map_zpowers]
    change zpowers (MulAut.conj (h:G) (u:G))=zpowers (a:G)
    rw [show MulAut.conj (h:G) (u:G)=((b:c.H):G) from congrArg Subtype.val hh]
    exact he
  refine ⟨h,?_⟩
  exact hcases.elim (fun hx => Or.inl (hgen ((orderOf_coe t.x).trans t.x_order) hx))
    (fun hy => Or.inr (hgen ((orderOf_coe t.y).trans t.y_order) hy))

theorem core_intersection_sylow_two_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27)
    (P : Sylow 2 (Subgroup.centralizer
      ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G))) :
    Nat.card P=2 := by
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  let C := Subgroup.centralizer (K:Set G)
  change Sylow 2 C at P
  have htwo : 2∣Nat.card C := by
    obtain ⟨v,_,hv,hvC⟩ := t.core_intersection_centralizing_involution hc
    have hd := orderOf_dvd_natCard (⟨v,hvC⟩:C)
    rw [←orderOf_coe (⟨v,hvC⟩:C)] at hd
    change orderOf v∣Nat.card C at hd
    rwa [hv] at hd
  have hPtwo : 2∣Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n:=1) (by simpa using htwo)
  have hnotfour : ¬4∣Nat.card P := by
    intro hfour
    have hfourle : 4≤Nat.card P := Nat.le_of_dvd Nat.card_pos hfour
    let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    let : Nontrivial (center P) := P.isPGroup'.center_nontrivial
    have hcenter := P.isPGroup'.to_subgroup (center P)
    obtain ⟨n,hn,hncard⟩ := hcenter.nontrivial_iff_card.mp inferInstance
    have hd : 2∣Nat.card (center P) := hncard ▸ dvd_pow_self 2 hn.ne'
    obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G:=center P) 2 hd
    let vG : G := (((v:P):C):G)
    have hvG : orderOf vG=2 := by
      dsimp only [vG]
      rw [orderOf_coe,orderOf_coe,orderOf_coe,hv]
    obtain ⟨g,hg⟩ := isConj_iff.mp (involutions_conjugate c vG (t.z:G) hvG
      ((orderOf_coe t.z).trans t.z_order))
    change MulAut.conj g vG=(t.z:G) at hg
    obtain ⟨k,hk⟩ := exists_prime_orderOf_dvd_card' (G:=K) 3
      (by rw [t.oddCore_intersection_card_of_twentySeven hc])
    have hkg : orderOf (k:G)=3 := (orderOf_coe k).trans hk
    have hgen : zpowers (k:G)=K := eq_of_le_of_card_ge (zpowers_le.mpr k.property)
      (by rw [Nat.card_zpowers,hkg,t.oddCore_intersection_card_of_twentySeven hc])
    let f : P →* G := (MulAut.conj g).toMonoidHom.comp
      (C.subtype.comp (P:Subgroup C).subtype)
    have hf : Function.Injective f := (MulAut.conj g).injective.comp
      (C.subtype_injective.comp (P:Subgroup C).subtype_injective)
    have hfH (p : P) : f p∈c.H := by
      rw [t.centralizer]
      apply mem_centralizer_singleton_iff.mpr
      have hvp : ((p:C):G)*vG=vG*((p:C):G) :=
        congrArg (fun w : P => ((w:C):G)) (mem_center_iff.mp v.property p)
      have hh := congrArg (MulAut.conj g) hvp
      change MulAut.conj g (((p:C):G))*(t.z:G)=(t.z:G)*MulAut.conj g (((p:C):G))
      simpa only [map_mul,hg] using hh
    let u : G := MulAut.conj g (k:G)
    have huH : u∈c.H := by
      rw [t.centralizer]
      apply mem_centralizer_singleton_iff.mpr
      have hkv : (k:G)*vG=vG*(k:G) := ((v:P):C).property k k.property
      have hh := congrArg (MulAut.conj g) hkv
      change MulAut.conj g (k:G)*(t.z:G)=(t.z:G)*MulAut.conj g (k:G)
      simpa only [map_mul,hg] using hh
    let uH : c.H := ⟨u,huH⟩
    let fH : P →* c.H := f.codRestrict c.H hfH
    have hfC (p : P) : fH p ∈ Subgroup.centralizer ({uH}:Set c.H) := by
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      change MulAut.conj g (((p:C):G))*MulAut.conj g (k:G) =
        MulAut.conj g (k:G)*MulAut.conj g (((p:C):G))
      have hh := congrArg (MulAut.conj g) (((p:C).property k k.property).symm)
      simpa only [map_mul] using hh
    let fC := fH.codRestrict (Subgroup.centralizer ({uH}:Set c.H)) hfC
    have hdiv : Nat.card P ∣ Nat.card (Subgroup.centralizer ({uH}:Set c.H)) :=
      card_dvd_of_injective fC (fun a b he => hf
        (congrArg (fun w : Subgroup.centralizer ({uH}:Set c.H) => ((w:c.H):G)) he))
    have hu3 : orderOf uH=3 := (orderOf_coe uH).symm.trans
      (((MulAut.conj g).orderOf_eq k).trans hkg)
    obtain ⟨h,hh⟩ := t.local_cubic_four_dvd_forces_factor uH hu3 (hfour.trans hdiv)
    have hmap : K.map (MulAut.conj (h*g)).toMonoidHom =
        (zpowers (uH:G)).map (MulAut.conj h).toMonoidHom := by
      rw [←hgen,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
      congr 1
      change (h*g)*(k:G)*(h*g)⁻¹=h*(g*(k:G)*g⁻¹)*h⁻¹
      group
    rcases hh with hh|hh
    · exact t.core_intersection_not_conjugate_left hc (h*g) (hmap.trans hh)
    · exact t.core_intersection_not_conjugate_right hc (h*g) (hmap.trans hh)
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have hnlt : n<2 := by
    by_contra he
    have hge : 2≤n := by omega
    apply hnotfour
    rw [hn]
    exact pow_dvd_pow 2 hge
  interval_cases n
  · rw [hn] at hPtwo
    norm_num at hPtwo
  · exact hn

theorem core_intersection_oddCore_index (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    let C := Subgroup.centralizer
      ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G)
    (pPrimeCore 2 C).index=2 ∧ 3^5∣Nat.card (pPrimeCore 2 C) := by
  let C := Subgroup.centralizer
    ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G)
  let P : Sylow 2 C := default
  have hP := t.core_intersection_sylow_two_card hc P
  have heven : 2∣Nat.card C := hP ▸ (P:Subgroup C).card_subgroup_dvd_card
  have hcompl := P.isComplement'_pPrimeCore_of_isCyclic (isCyclic_of_prime_card hP) heven
  have hprod := hcompl.card_mul_card
  change Nat.card P*Nat.card (pPrimeCore 2 C)=Nat.card C at hprod
  rw [hP] at hprod
  constructor
  · change (pPrimeCore 2 C).index=2
    have hh := (pPrimeCore 2 C).card_mul_index
    have hpos : 0<Nat.card (pPrimeCore 2 C) := Nat.card_pos
    nlinarith
  · have hd := t.core_intersection_centralizer_fifth_power_dvd hc
    change 3^5∣Nat.card C at hd
    rw [←hprod] at hd
    exact (by decide : Nat.Coprime (3^5) 2).dvd_of_dvd_mul_left hd

include c in
private theorem odd_fixed_card_dvd_nine (D : Subgroup G) (hD : Odd (Nat.card D))
    (v : G) (hv : orderOf v=2) :
    Nat.card (D ⊓ Subgroup.centralizer ({v}:Set G) : Subgroup G) ∣ 9 := by
  let F := D ⊓ Subgroup.centralizer ({v}:Set G)
  have ho : Odd (Nat.card F) := hD.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hd : Nat.card F ∣ 64*9 := by
    have hh := card_dvd_of_le (show F≤Subgroup.centralizer ({v}:Set G) from inf_le_right)
    rwa [involution_centralizer_card c v hv] at hh
  exact (ho.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hd

theorem core_intersection_oddCore_card_dvd (t : CubicTorus c) :
    let C := Subgroup.centralizer
      ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G)
    Nat.card (pPrimeCore 2 C) ∣ 3^6 := by
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  let C := Subgroup.centralizer (K:Set G)
  let D := (pPrimeCore 2 C).map C.subtype
  have hDcard : Nat.card D=Nat.card (pPrimeCore 2 C) := card_map_of_injective C.subtype_injective
  have hD : Odd (Nat.card D) := by
    rw [hDcard]
    exact Nat.Coprime.odd_of_left pPrimeCore_coprime_card
  have hTN : t.torus.map c.H.subtype ≤ normalizer (D:Set G) :=
    t.torus_normalizes_core_intersection.trans
      ((normalizer_le_normalizer_centralizer K).trans
        (normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C)))
  have hzT : (t.z:G)∈t.torus.map c.H.subtype := mem_map_of_mem c.H.subtype
    (mem_sup_left (mem_zpowers _))
  have hnT : (t.n:G)∈t.torus.map c.H.subtype := mem_map_of_mem c.H.subtype
    (mem_sup_right (mem_zpowers _))
  let a : normalizer (D:Set G) := ⟨t.z,hTN hzT⟩
  let b : normalizer (D:Set G) := ⟨t.n,hTN hnT⟩
  have ha : a^2=1 := Subtype.ext (by
    change (t.z:G)^2=1
    simpa only [orderOf_coe,t.z_order] using pow_orderOf_eq_one (t.z:G))
  have hb : b^2=1 := Subtype.ext (by
    change (t.n:G)^2=1
    simpa only [orderOf_coe,t.n_order] using pow_orderOf_eq_one (t.n:G))
  have hab : Commute a b := Subtype.ext
    (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.n.property)).symm
  have hzn : t.z≠t.n := by
    intro he
    apply t.outside
    rw [←he]
    exact mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1)
  have hab2 : orderOf ((a*b:normalizer (D:Set G)):G)=2 := by
    have hp : (((a*b:normalizer (D:Set G)):G))^2=1 := by
      have hh := hab.mul_pow 2
      rw [ha,hb,one_mul] at hh
      exact congrArg Subtype.val hh
    have hne : (((a*b:normalizer (D:Set G)):G))≠1 := by
      intro hh
      have hni : (t.n:G)⁻¹=(t.n:G) := inv_eq_of_mul_eq_one_left
        (by simpa only [orderOf_coe,t.n_order,pow_two] using pow_orderOf_eq_one (t.n:G))
      exact hzn (Subtype.ext ((eq_inv_of_mul_eq_one_left hh).trans hni))
    exact orderOf_eq_prime hp hne
  have hformula := D.card_three_odd_centralizers hD a b ha hb hab
  have hd : Nat.card D ∣
      Nat.card (D ⊓ Subgroup.centralizer ({(a:G)}:Set G) : Subgroup G) *
      Nat.card (D ⊓ Subgroup.centralizer ({(b:G)}:Set G) : Subgroup G) *
      Nat.card (D ⊓ Subgroup.centralizer ({((a*b:normalizer (D:Set G)):G)}:Set G) : Subgroup G) := by
    rw [←hformula]
    exact dvd_mul_right _ _
  have hx := odd_fixed_card_dvd_nine (c:=c) D hD (t.z:G) ((orderOf_coe t.z).trans t.z_order)
  have hy := odd_fixed_card_dvd_nine (c:=c) D hD (t.n:G) ((orderOf_coe t.n).trans t.n_order)
  have hz := odd_fixed_card_dvd_nine (c:=c) D hD ((a*b:normalizer (D:Set G)):G) hab2
  have hbig := hd.trans (Nat.mul_dvd_mul (Nat.mul_dvd_mul hx hy) hz)
  change Nat.card (pPrimeCore 2 C) ∣ 3^6
  rwa [hDcard] at hbig

theorem core_intersection_centralizer_orders (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    let C := Subgroup.centralizer
      ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G)
    (Nat.card (pPrimeCore 2 C)=243 ∨ Nat.card (pPrimeCore 2 C)=729) ∧
      (Nat.card C=486 ∨ Nat.card C=1458) := by
  let C := Subgroup.centralizer
    ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G)
  have hd := t.core_intersection_oddCore_card_dvd
  change Nat.card (pPrimeCore 2 C)∣3^6 at hd
  obtain ⟨hi,hlarge⟩ := t.core_intersection_oddCore_index hc
  change (pPrimeCore 2 C).index=2 at hi
  change 3^5∣Nat.card (pPrimeCore 2 C) at hlarge
  obtain ⟨n,hn⟩ := (IsPGroup.of_card_dvd_pow (p:=3) (n:=6) hd).exists_card_eq
  have hnle : n≤6 := (Nat.pow_le_pow_iff_right (by decide : 1<3)).mp
    (Nat.le_of_dvd (by decide : 0<3^6) (hn ▸ hd))
  have hnge : 5≤n := (Nat.pow_le_pow_iff_right (by decide : 1<3)).mp
    (hn ▸ Nat.le_of_dvd Nat.card_pos hlarge)
  have hcases : Nat.card (pPrimeCore 2 C)=243 ∨ Nat.card (pPrimeCore 2 C)=729 := by
    interval_cases n
    · exact Or.inl hn
    · exact Or.inr hn
  refine ⟨hcases,?_⟩
  have hprod := (pPrimeCore 2 C).card_mul_index
  rw [hi] at hprod
  rcases hcases with h|h
  · left
    change Nat.card C=486
    rw [h] at hprod
    exact hprod.symm
  · right
    change Nat.card C=1458
    rw [h] at hprod
    exact hprod.symm

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
