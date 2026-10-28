module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Transport
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Split.Lifting

/-!
# Excluding the marked direct-product normalizer

For the central-factor lift u, every inverter of B is C_G(B)-conjugate to u
or zu. Cubic correction replaces conjugators by elements centralizing u, and
shows that the orbit of u under C_G(B) is its B-orbit. The original outer SD16
reflection then identifies the zu-orbit as the z-class. Transporting any
H-member of the s-class to an inverter yields the required H-conjugator.

Consequently the literal T_s is Sylow in C_G(s), of exponent four. But u is
s-conjugate and centralizes the original SD16 subgroup, which contains an
element of order eight. This contradiction excludes the split alternative.
The argument retains all B-conjugates and does not use the false printed
singleton assertion for the u-orbit.

Source: Aschbacher–Smith J.2.7(3), printed p.436 (PDF p.447).
-/

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

lemma modular_inverter_mem_H (u : G) (hmod : ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B) :
    u ∈ d.toTypeRuSetup.H := by
  rw [c.H_eq_centralizer_z, mem_centralizer_singleton_iff]
  exact c.commute_of_modular_cubic_of_coprime_power u hmod c.z c.z_mem_GB 2
    (by decide) ((SourceCompletion.z_order c) ▸ pow_orderOf_eq_one c.z)

lemma modular_inverter_mem_K (u : G) (hu2 : orderOf u=2)
    (hmod : ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B) : u ∈ d.toTypeRuSetup.K := by
  apply c.involution_mem_K_of_centralizes_quaternion u (c.modular_inverter_mem_H u hmod) hu2
  intro x hx
  have hpow : x^2048=1 := by
    have hh := pow_card_eq_one' (x := (⟨x,hx.1⟩ : d.toTypeRuSetup.Q))
    rw [d.ru2.card_Q d.card_Z] at hh
    exact congrArg Subtype.val hh
  exact c.commute_of_modular_cubic_of_coprime_power u hmod x hx.2 2048 (by decide) hpow

lemma modular_inverter_centralizes_TB (u : G)
    (hmod : ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B) (t : CubicLocalTwo c) :
    t.TB.map c.GB.subtype ≤ centralizer ({u} : Set G) := by
  rintro x ⟨y,hy,rfl⟩
  have hpow : (y : G)^16=1 := by
    have hh := pow_card_eq_one' (x := (⟨y,hy⟩ : t.TB))
    rw [Nat.card_congr t.marking.toEquiv, Semidihedral.standardModel_card] at hh
    exact congrArg (fun a : t.TB => ((a : c.GB) : G)) hh
  apply mem_centralizer_singleton_iff.mpr
  exact (c.commute_of_modular_cubic_of_coprime_power u hmod y y.property 16 (by decide) hpow).symm

lemma centralizing_conjugator_of_modular_inverter (u : G) (hui : c.InvertsB u)
    (hmod : ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B)
    (x y g : G) (hy : y ∈ c.GB) (hg : g ∈ c.GB) (he : g*x*g⁻¹=y) :
    ∃ a ∈ c.GB, Commute u a ∧ a*x*a⁻¹=y := by
  obtain ⟨b,hb,a,ha,hua,hg'⟩ := c.cubic_factor_of_modular_inverter u hui hmod g hg
  refine ⟨a,ha,hua,?_⟩
  calc
    a*x*a⁻¹ = b⁻¹*(g*x*g⁻¹)*b := by rw [hg']; group
    _ = b⁻¹*y*b := by rw [he]
    _ = y := by rw [mul_assoc, ← hy b hb]; group

lemma conjugation_of_modular_inverter (u : G) (hui : c.InvertsB u)
    (hmod : ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B) (g : G) (hg : g ∈ c.GB) :
    ∃ b ∈ c.B, g*u*g⁻¹=b*u*b⁻¹ := by
  obtain ⟨b,hb,a,_,hua,hg'⟩ := c.cubic_factor_of_modular_inverter u hui hmod g hg
  refine ⟨b,hb,?_⟩
  calc
    g*u*g⁻¹=b*(a*u*a⁻¹)*b⁻¹ := by rw [hg']; group
    _=b*u*b⁻¹ := by rw [hua.symm.mul_inv_cancel]

lemma cubic_conjugate_inverter (u : G) (hui : c.InvertsB u) (b : G) (hb : b∈c.B) :
    b^2*u*(b^2)⁻¹=b*u := by
  have hb3 : b^3=1 := by
    have hh := pow_card_eq_one' (x := (⟨b,hb⟩ : c.B))
    rw [SourceCompletion.B_card c] at hh
    exact congrArg Subtype.val hh
  calc
    b^2*u*(b^2)⁻¹ = b^2*(u*(b^2)⁻¹*u⁻¹)*u := by group
    _ = b^2*b^2*u := by rw [hui _ (c.B.inv_mem (c.B.pow_mem hb 2)), inv_inv]
    _ = b^3*b*u := by group
    _ = b*u := by rw [hb3, one_mul]


lemma source_cubic_involution_conjugator (x : G) (hx : x∈c.GB) (hx2 : orderOf x=2) :
    ∃ g∈c.GB, g*x*g⁻¹=c.z := by
  obtain ⟨t⟩ := SourceCompletion.cubicLocalTwo c
  obtain ⟨b,hb,hcontrol⟩ := SourceCompletion.cubic_generator_fusion c
  have hh := c.involutions_GB_isConj t (SourceCompletion.fusion c).2.2.1 b hb hcontrol
    ⟨x,hx⟩ ((Subgroup.orderOf_coe ⟨x,hx⟩).symm.trans hx2)
  obtain ⟨g,hg⟩ := isConj_iff.mp hh
  exact ⟨g,g.property,congrArg Subtype.val hg⟩

lemma inverter_orbits_of_modular_inverter (u : G) (hu2 : orderOf u=2)
    (hui : c.InvertsB u) (hmod : ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B)
    (v : G) (hv2 : orderOf v=2) (hvi : c.InvertsB v) :
    ∃ g∈c.GB, g*v*g⁻¹=u ∨ g*v*g⁻¹=c.z*u := by
  have hupow : u^2=1 := hu2 ▸ pow_orderOf_eq_one u
  have hvpow : v^2=1 := hv2 ▸ pow_orderOf_eq_one v
  have hvu : v*u∈c.GB := by
    intro b hb
    have he : (v*u)*b*(v*u)⁻¹=b := by
      calc
        (v*u)*b*(v*u)⁻¹=v*(u*b*u⁻¹)*v⁻¹ := by group
        _=v*b⁻¹*v⁻¹ := by rw [hui b hb]
        _=b := by rw [hvi _ (c.B.inv_mem hb),inv_inv]
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨b,hb,x,hx,hux,hfac⟩ := c.cubic_factor_of_modular_inverter u hui hmod (v*u) hvu
  have hvfac : v=b*x*u := by
    calc v=(v*u)*u := by rw [mul_assoc,←pow_two,hupow,mul_one]
         _=b*x*u := by rw [hfac]
  have hprod : (b*x*u)^2=x^2 := by
    calc
      (b*x*u)^2=b*x*(u*b*u⁻¹)*(u*x*u⁻¹)*u^2 := by simp only [pow_two]; group
      _=b*x*b⁻¹*x := by rw [hui b hb,hux.mul_inv_cancel,hupow,mul_one]
      _=x^2 := by rw [hx b hb,pow_two]; group
  have hxpow : x^2=1 := by rw [←hprod,←hvfac]; exact hvpow
  have hconjx : b^2*x*(b^2)⁻¹=x :=
    mul_inv_eq_iff_eq_mul.mpr (hx _ (c.B.pow_mem hb 2))
  have hconjv : b^2*(x*u)*(b^2)⁻¹=v := by
    calc
      b^2*(x*u)*(b^2)⁻¹=(b^2*x*(b^2)⁻¹)*(b^2*u*(b^2)⁻¹) := by group
      _=x*(b*u) := by rw [hconjx,c.cubic_conjugate_inverter u hui b hb]
      _=b*x*u := by rw [←mul_assoc,←hx b hb]
      _=v := hvfac.symm
  let g0 := (b^2)⁻¹
  have hg0 : g0∈c.GB := (c.B_le_GB_of_card (SourceCompletion.B_card c))
    (c.B.inv_mem (c.B.pow_mem hb 2))
  have hg0v : g0*v*g0⁻¹=x*u := by dsimp [g0]; rw [←hconjv]; group
  by_cases hx1 : x=1
  · exact ⟨g0,hg0,Or.inl (by simpa only [hx1,one_mul] using hg0v)⟩
  · obtain ⟨g,hg,hgx⟩ := c.source_cubic_involution_conjugator x hx
      (orderOf_eq_prime hxpow hx1)
    obtain ⟨a,ha,hua,hax⟩ := c.centralizing_conjugator_of_modular_inverter
      u hui hmod x c.z g c.z_mem_GB hg hgx
    refine ⟨a*g0,c.GB.mul_mem ha hg0,Or.inr ?_⟩
    calc
      (a*g0)*v*(a*g0)⁻¹=a*(g0*v*g0⁻¹)*a⁻¹ := by group
      _=a*(x*u)*a⁻¹ := by rw [hg0v]
      _=(a*x*a⁻¹)*(a*u*a⁻¹) := by group
      _=c.z*u := by rw [hax,hua.symm.mul_inv_cancel]


lemma modular_inverter_z_product_fused (u : G) (hu2 : orderOf u=2)
    (hui : c.InvertsB u) (hmod : ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B) :
    IsConj (c.z*u) c.z := by
  obtain ⟨t⟩ := SourceCompletion.cubicLocalTwo c
  let j : t.TB := t.marking.symm (Semidihedral.standardReflection 4 (Nat.le_refl 4))
  let r : G := ((j : c.GB) : G)
  have hrGB : r∈c.GB := (j : c.GB).property
  have hrH : r∈d.toTypeRuSetup.H := by
    have hjC : (j : c.GB) ∈ centralizer ({c.zInGB} : Set c.GB) := map_subtype_le _ j.property
    rwa [c.localCentralizer_eq] at hjC
  have hr2 : orderOf r=2 := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
    exact (t.marking.symm.orderOf_eq _).trans (Semidihedral.standardReflection_order 4 (Nat.le_refl 4))
  have huH := c.modular_inverter_mem_H u hmod
  have huK := c.modular_inverter_mem_K u hu2 hmod
  have hruH : r*u∈d.toTypeRuSetup.H := d.toTypeRuSetup.H.mul_mem hrH huH
  have hruK : r*u∉d.toTypeRuSetup.K := by
    intro hh
    have h := d.toTypeRuSetup.K.mul_mem hh (d.toTypeRuSetup.K.inv_mem huK)
    exact t.reflection_outside (by simpa only [mul_inv_cancel_right] using h)
  have hur : Commute u r := c.commute_of_modular_cubic_of_coprime_power
    u hmod r hrGB 2 (by decide) (hr2 ▸ pow_orderOf_eq_one r)
  have hrpow : r^2=1 := hr2 ▸ pow_orderOf_eq_one r
  have hupow : u^2=1 := hu2 ▸ pow_orderOf_eq_one u
  have hru2 : orderOf (r*u)=2 := orderOf_eq_prime (by
    rw [hur.symm.mul_pow,hrpow,hupow,one_mul])
    (fun h => hruK (h ▸ d.toTypeRuSetup.K.one_mem))
  have hruz : IsConj (r*u) c.z := (SourceCompletion.fusion c).2.2.1.1.2.2
    (r*u) ⟨hruH,hruK,hru2⟩
  obtain ⟨g,hg,hgr⟩ := c.source_cubic_involution_conjugator r hrGB hr2
  obtain ⟨a,ha,hua,har⟩ := c.centralizing_conjugator_of_modular_inverter
    u hui hmod r c.z g c.z_mem_GB hg hgr
  have hz : IsConj (r*u) (c.z*u) := isConj_iff.mpr ⟨a, by
    calc
      a*(r*u)*a⁻¹=(a*r*a⁻¹)*(a*u*a⁻¹) := by group
      _=c.z*u := by rw [har,hua.symm.mul_inv_cancel]⟩
  exact hz.symm.trans hruz

lemma H_s_conjugates_to_modular_inverter (u : G) (hu2 : orderOf u=2)
    (hui : c.InvertsB u) (hmod : ∀ x ∈ c.GB, ⁅u,x⁆ ∈ c.B)
    (x : G) (hxH : x∈d.toTypeRuSetup.H) (hsx : IsConj c.s x) :
    ∃ h∈d.toTypeRuSetup.H, h*x*h⁻¹=u := by
  have hxQ := (c.s_conjugate_mem_K_sdiff_Q (SourceCompletion.fusion c).2.2.1 hxH hsx).2
  have hx2 : orderOf x=2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hsx
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq _).trans c.s_order_source
  obtain ⟨k,hk,hki⟩ := c.H_inverter_transport_source x hxH hxQ hx2
  let v := k*x*k⁻¹
  have hv2 : orderOf v=2 := ((MulAut.conj k).orderOf_eq x).trans hx2
  have hxv : IsConj x v := isConj_iff.mpr ⟨k,rfl⟩
  obtain ⟨a,ha,hav | hav⟩ := c.inverter_orbits_of_modular_inverter u hu2 hui hmod v hv2 hki
  · obtain ⟨b,hb,hab⟩ := c.conjugation_of_modular_inverter u hui hmod a⁻¹ (c.GB.inv_mem ha)
    have hvb : v=b*u*b⁻¹ := by
      calc
        v=a⁻¹*(a*v*a⁻¹)*a := by group
        _=a⁻¹*u*a := by rw [hav]
        _=b*u*b⁻¹ := by simpa only [inv_inv] using hab
    refine ⟨b⁻¹*k,d.toTypeRuSetup.H.mul_mem
      (d.toTypeRuSetup.H.inv_mem (c.B_le_H hb)) hk,?_⟩
    calc
      (b⁻¹*k)*x*(b⁻¹*k)⁻¹=b⁻¹*v*b := by dsimp [v]; group
      _=u := by rw [hvb]; group
  · have hsv : IsConj c.s (c.z*u) := hsx.trans (hxv.trans (isConj_iff.mpr ⟨a,hav⟩))
    exact (c.not_isConj_z_s_source
      (hsv.trans (c.modular_inverter_z_product_fused u hu2 hui hmod)).symm).elim


/-- The original type-Ru source excludes the marked C₂ × M₁₀ alternative. -/
public theorem not_normalizer_split_source
    (e : c.NormalizerQuotient ≃* (Multiplicative (ZMod 2) × AlternatingSix.M10.extension))
    (hM : c.centralizerImage.map e.toMonoidHom =
      (⊥ : Subgroup (Multiplicative (ZMod 2))).prod ⊤) : False := by
  obtain ⟨u,hu2,hui,hmod⟩ := c.exists_central_quotient_inverter_of_split e hM
  have hsH : c.s∈d.toTypeRuSetup.H := d.S_le_H c.s_mem.1
  obtain ⟨h0,hh0,h0s⟩ := c.H_s_conjugates_to_modular_inverter
    u hu2 hui hmod c.s hsH (IsConj.refl c.s)
  have hsu : IsConj c.s u := isConj_iff.mpr ⟨h0,h0s⟩
  have hf : ∀ x∈d.toTypeRuSetup.H, IsConj c.s x →
      ∃ h∈d.toTypeRuSetup.H, h*c.s*h⁻¹=x := by
    intro x hx hsx
    obtain ⟨h,hh,he⟩ := c.H_s_conjugates_to_modular_inverter u hu2 hui hmod x hx hsx
    refine ⟨h⁻¹*h0,d.toTypeRuSetup.H.mul_mem (d.toTypeRuSetup.H.inv_mem hh) hh0,?_⟩
    calc
      (h⁻¹*h0)*c.s*(h⁻¹*h0)⁻¹=h⁻¹*(h0*c.s*h0⁻¹)*h := by group
      _=h⁻¹*u*h := by rw [h0s]
      _=x := by rw [←he]; group
  obtain ⟨t⟩ := SourceCompletion.cubicLocalTwo c
  exact c.not_TB_centralizes_s_conjugate t (SourceCompletion.H_inf_Gs_eq_Ts c) hf hsu
    (c.modular_inverter_centralizes_TB u hmod t)

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
