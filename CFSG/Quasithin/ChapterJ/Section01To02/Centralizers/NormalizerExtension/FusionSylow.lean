module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.LocalTwo
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Sylow promotion and the exponent contradiction for J.2.7(3)

Suppose C_H(s) = T_s and H controls the fusion of s into H. A Sylow subgroup
of C_G(s) containing T_s can be conjugated into the original ambient Sylow.
Correcting that conjugator inside H embeds it back into T_s. Comparing orders
proves that the original T_s is Sylow, with no replacement of its embedding.
J.2.3 gives exponent four, so no conjugate s-centralizer contains an element
of order eight. Applied to the original marked SD16 subgroup T_B, this is the
terminal contradiction in the split-extension case.

The centralizer equality and fusion control are explicit premises here.
The split-case orbit argument must establish the latter before this
contradiction proves exclusion of Z2 x M10.

Source: Aschbacher–Smith, J.2.7(3), printed p.436 (PDF p.447).
-/

public section
open Subgroup
open scoped Pointwise

private theorem sylow_of_local_fusion
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (x : G) (hxH : x ∈ H)
    (hQ : IsPGroup 2 (H ⊓ centralizer ({x} : Set G) : Subgroup G))
    (hf : ∀ y ∈ H, IsConj x y → ∃ h ∈ H, h*x*h⁻¹ = y) :
    ∃ P : Sylow 2 (centralizer ({x} : Set G)),
      (P : Subgroup (centralizer ({x} : Set G))) =
        H.subgroupOf (centralizer ({x} : Set G)) := by
  let C := centralizer ({x} : Set G)
  let Q := H ⊓ C
  have hQC : Q ≤ C := inf_le_right
  obtain ⟨P, hP⟩ := (hQ.comap_subtype (K := C)).exists_le_sylow
  let R := (P : Subgroup C).map C.subtype
  have hQR : Q ≤ R := by
    rw [← map_subgroupOf_eq_of_le hQC]
    exact map_mono hP
  have hxR : x ∈ R := hQR ⟨hxH, mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨U, hU⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U T
  let a : G ≃* G := MulAut.conj g
  have haT : R.map a.toMonoidHom ≤ (T : Subgroup G) := by
    rw [← hg]
    exact map_mono hU
  have hayH : a x ∈ H := hTH (haT (mem_map_of_mem a.toMonoidHom hxR))
  obtain ⟨h, hh, hhx⟩ := hf (a x) hayH (isConj_iff.mpr ⟨g, rfl⟩)
  let b : G ≃* G := a.trans (MulAut.conj h⁻¹)
  have hbx : b x = x := by
    change h⁻¹ * (a x) * (h⁻¹)⁻¹ = x
    rw [← hhx]
    group
  have hbQ : R.map b.toMonoidHom ≤ Q := by
    rintro y ⟨r, hr, rfl⟩
    constructor
    · exact H.mul_mem (H.mul_mem (H.inv_mem hh)
        (hTH (haT (mem_map_of_mem a.toMonoidHom hr)))) (H.inv_mem (H.inv_mem hh))
    · apply mem_centralizer_singleton_iff.mpr
      have hrC : r ∈ C := map_subtype_le _ hr
      have he := congrArg b (mem_centralizer_singleton_iff.mp hrC)
      change b r * x = x * b r
      simpa only [map_mul, hbx] using he
  have heq : Q = R := eq_of_le_of_card_ge hQR (by
    have hc := card_le_of_le hbQ
    rwa [card_map_of_injective b.injective] at hc)
  refine ⟨P, ?_⟩
  apply Subgroup.map_injective C.subtype_injective
  change R = (H.subgroupOf C).map C.subtype
  simpa only [subgroupOf_map_subtype] using heq.symm



namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

private def singer : SpecialCore.SingerChoice d.toTypeRuSetup c.sylowThree :=
  ⟨c.B7, c.B7_le, c.B7_card, c.B_normalizes⟩

/-- The J.2.3 exponent bound for the literal subgroup C_S(s). -/
theorem Ts_exponent_source : Monoid.exponent c.Ts = 4 :=
  ((c.singer.source_conclusions d c.sylowThree).three c.s c.s_mem c.s_ne_one).2.2.2.2

/-- The chosen nonidentity element of the fixed four-group is an involution. -/
theorem s_order_source : orderOf c.s = 2 := by
  let e : c.S0 ≃* Multiplicative (ZMod 2 × ZMod 2) :=
    c.singer.fixedCoreEquivFour d.toTypeRuSetup c.sylowThree
  have hs : (⟨c.s, c.s_mem⟩ : c.S0) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, pow_two]
    change (e ⟨c.s, c.s_mem⟩).toAdd + (e ⟨c.s, c.s_mem⟩).toAdd = 0
    exact CharTwo.add_self_eq_zero _
  exact orderOf_eq_prime (congrArg Subtype.val hs) c.s_ne_one

/-- J.2.3 separates the two distinguished involutions. -/
theorem not_isConj_z_s_source : ¬ IsConj c.z c.s := by
  have hz1 : c.z ≠ 1 := by
    intro hz
    have he := c.z_generator
    rw [hz, zpowers_one_eq_bot] at he
    have hc := d.card_Z
    simp [he] at hc
  exact SpecialCore.not_isConj_of_mem_fixedCore d.toTypeRuSetup d.card_Z
    c.B7 c.B7_card c.z c.z_mem_Z hz1 c.s c.s_mem

/-- Earlier involution fusion puts every H-member of the s-class in K minus Q. -/
theorem s_conjugate_mem_K_sdiff_Q
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    {u : G} (huH : u ∈ d.toTypeRuSetup.H) (hsu : IsConj c.s u) :
    u ∈ d.toTypeRuSetup.K ∧ u ∉ d.toTypeRuSetup.Q := by
  have hu2 : orderOf u = 2 := by
    obtain ⟨a, ha⟩ := isConj_iff.mp hsu
    rw [← ha]
    exact ((MulAut.conj a).orderOf_eq c.s).trans c.s_order_source
  have hn : ¬ IsConj u c.z := fun h => c.not_isConj_z_s_source (hsu.trans h).symm
  constructor
  · by_contra huK
    exact hn (h26.1.2.2 u ⟨huH, huK, hu2⟩)
  · intro huQ
    exact hn (h26.2.2.1 u huQ hu2)

/-- Controlled s-fusion and C_H(s) = T_s promote the literal subgroup to Sylow in C_G(s). -/
theorem Ts_sylow_of_H_fusion
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (hf : ∀ u ∈ d.toTypeRuSetup.H, IsConj c.s u →
      ∃ h ∈ d.toTypeRuSetup.H, h*c.s*h⁻¹ = u) :
    ∃ P : Sylow 2 c.Gs, (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs := by
  have hsH : c.s ∈ d.toTypeRuSetup.H :=
    d.toTypeRuSetup.T_le_H (d.S_le_T c.s_mem.1)
  have hQ : IsPGroup 2 (d.toTypeRuSetup.H ⊓ c.Gs : Subgroup G) := by
    rw [hHs]
    exact (isPGroup_pCoreIn 2 d.L).to_le inf_le_left
  obtain ⟨P, hP⟩ := sylow_of_local_fusion d.T d.toTypeRuSetup.H
    d.toTypeRuSetup.T_le_H c.s hsH hQ hf
  refine ⟨P, hP.trans ?_⟩
  rw [← hHs]
  ext x
  exact ⟨fun hx => ⟨hx, x.property⟩, And.left⟩

/-- Every conjugate s-centralizer excludes order eight once local fusion is controlled. -/
theorem no_order_eight_of_H_fusion
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (hf : ∀ u ∈ d.toTypeRuSetup.H, IsConj c.s u →
      ∃ h ∈ d.toTypeRuSetup.H, h*c.s*h⁻¹ = u)
    {u : G} (hsu : IsConj c.s u) {x : G}
    (hx : x ∈ centralizer ({u} : Set G)) : orderOf x ≠ 8 := by
  intro hx8
  obtain ⟨g, hg⟩ := isConj_iff.mp hsu
  let a : G ≃* G := MulAut.conj g⁻¹
  have has : a u = c.s := by
    change g⁻¹ * u * (g⁻¹)⁻¹ = c.s
    rw [← hg]
    group
  have hxC : a x ∈ c.Gs := by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg a (mem_centralizer_singleton_iff.mp hx)
    simpa only [map_mul, has] using he
  let y : c.Gs := ⟨a x, hxC⟩
  have hy8 : orderOf y = 2 ^ 3 := by
    rw [← Subgroup.orderOf_coe]
    exact (a.orderOf_eq x).trans hx8
  obtain ⟨P, hP⟩ := c.Ts_sylow_of_H_fusion hHs hf
  obtain ⟨v, hv⟩ := P.exists_isConj_of_orderOf_eq_prime_pow hy8
  have hvTs : ((v : c.Gs) : G) ∈ c.Ts := by
    have hm : (v : c.Gs) ∈ (P : Subgroup c.Gs) := v.property
    rw [hP] at hm
    exact hm
  have hv8 : orderOf ((v : c.Gs) : G) = 8 := by
    rw [Subgroup.orderOf_coe]
    obtain ⟨k, hk⟩ := isConj_iff.mp hv
    rw [← hk]
    exact ((MulAut.conj k).orderOf_eq y).trans hy8
  have hd := orderOf_dvd_of_pow_eq_one (Subgroup.pow_exponent_eq_one hvTs)
  rw [hv8, c.Ts_exponent_source] at hd
  norm_num at hd

/-- The original SD16 subgroup cannot centralize an s-conjugate after Sylow promotion. -/
theorem not_TB_centralizes_s_conjugate
    (t : CubicLocalTwo c)
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (hf : ∀ u ∈ d.toTypeRuSetup.H, IsConj c.s u →
      ∃ h ∈ d.toTypeRuSetup.H, h*c.s*h⁻¹ = u)
    {u : G} (hsu : IsConj c.s u) :
    ¬ t.TB.map c.GB.subtype ≤ centralizer ({u} : Set G) := by
  intro hle
  let r := t.marking.symm (Semidihedral.standardRotation 4 (Nat.le_refl 4))
  have hr : ((r : c.GB) : G) ∈ t.TB.map c.GB.subtype := mem_map_of_mem _ r.property
  apply c.no_order_eight_of_H_fusion hHs hf hsu (hle hr)
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  exact (t.marking.symm.orderOf_eq _).trans (Semidihedral.standardRotation_order 4 (Nat.le_refl 4))

end CFSG.Quasithin.ChapterJ.Centralizers.Choices

