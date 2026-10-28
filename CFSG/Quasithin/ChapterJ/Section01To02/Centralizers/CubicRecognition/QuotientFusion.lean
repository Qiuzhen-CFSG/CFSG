module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.LocalTwo

/-!
# Fusion inside the cubic centralizer and its actual quotient

A.1.7(1) corrects an ambient conjugator using control of a generator of B
inside H = C_G(z). The corrected conjugator centralizes B, proving that
the already fused involutions form one class inside C_G(B). The premise
about generator fusion in H remains explicit; it is not fusion in C_G(B).
Its earlier-source producer is the H/Sylow-three local structure in J.2.1–6.

For the quotient by B of order three, cubing an arbitrary lift of an
involution produces an involution with the same image. Thus the actual
quotient inherits the single involution class.

Source: Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446).
-/

public section
noncomputable section

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- A.1.7(1) in the cubic centralizer: control of the generator's fusion in H
corrects an ambient conjugator into C_G(B). The premise concerns fusion in H,
not the desired fusion in C_G(B). -/
theorem isConj_in_GB (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b)
    (i : c.GB) (hi : IsConj (i : G) c.z) : IsConj i c.zInGB := by
  have hbB : b ∈ c.B := hb ▸ mem_zpowers b
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  let x := (MulAut.conj g) b
  have hxH : x ∈ d.toTypeRuSetup.H := by
    rw [c.H_eq_centralizer_z, mem_centralizer_singleton_iff]
    have he := congrArg (MulAut.conj g) (i.property b hbB)
    simpa only [x, map_mul, MulAut.conj_apply, hg] using he
  obtain ⟨h, hh⟩ := hcontrol x hxH (isConj_iff.mpr ⟨g, rfl⟩)
  have hcb : (h : G) * g ∈ c.GB := by
    change (h : G) * g ∈ centralizer (c.B : Set G)
    rw [hb, zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    apply mul_inv_eq_iff_eq_mul.mp
    simpa only [x, MulAut.conj_apply, mul_inv_rev, mul_assoc] using hh
  refine isConj_iff.mpr ⟨⟨(h : G) * g, hcb⟩, Subtype.ext ?_⟩
  change ((h : G) * g) * (i : G) * ((h : G) * g)⁻¹ = c.z
  calc
    _ = (h : G) * (g * (i : G) * g⁻¹) * (h : G)⁻¹ := by group
    _ = (h : G) * c.z * (h : G)⁻¹ := by rw [hg]
    _ = c.z := mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ h.property))

/-- The one-class statement inside the actual centralizer, prior to transfer. -/
theorem involutions_GB_isConj (t : CubicLocalTwo c)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z) (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b)
    (i : c.GB) (hi : orderOf i = 2) : IsConj i c.zInGB := by
  exact c.isConj_in_GB b hb hcontrol i (t.involutions_GB_fused h26 i i.property
    ((Subgroup.orderOf_coe i).trans hi))

/-- An involution in the quotient by B has an involution lift: cube any lift.
The kernel order is three, so its sixth power is one. -/
theorem exists_involution_lift (hB : Nat.card c.B = 3)
    (x : c.CubicQuotient) (hx : orderOf x = 2) :
    ∃ y : c.GB, orderOf y = 2 ∧ c.cubicQuotientMap y = x := by
  obtain ⟨y, rfl⟩ := c.cubicQuotientMap_surjective x
  have hx2 : (c.cubicQuotientMap y)^2 = 1 := hx ▸ pow_orderOf_eq_one _
  have hk : y^2 ∈ c.cubicKernel := by
    rw [← c.cubicQuotientMap_ker]
    exact (map_pow c.cubicQuotientMap y 2).trans hx2
  have hy6 : (y^3)^2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨y^2, hk⟩ : c.cubicKernel))
    rw [c.cubicKernel_card hB] at hh
    have hh' := congrArg Subtype.val hh
    change (y^2)^3 = 1 at hh'
    simpa only [← pow_mul] using hh'
  have hmap : c.cubicQuotientMap (y^3) = c.cubicQuotientMap y := by
    rw [map_pow, show 3 = 2+1 from rfl, pow_succ, hx2, one_mul]
  refine ⟨y^3, orderOf_eq_prime hy6 ?_, hmap⟩
  intro he
  have hone : c.cubicQuotientMap y = 1 := by rw [← hmap, he, map_one]
  simp [hone] at hx

/-- The literal quotient inherits one involution class from C_G(B). -/
theorem involutions_cubicQuotient_isConj (hB : Nat.card c.B = 3)
    (t : CubicLocalTwo c) (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b)
    (x : c.CubicQuotient) (hx : orderOf x = 2) :
    IsConj x (c.cubicQuotientMap c.zInGB) := by
  obtain ⟨y, hy, rfl⟩ := c.exists_involution_lift hB x hx
  exact c.cubicQuotientMap.map_isConj (c.involutions_GB_isConj t h26 b hb hcontrol y hy)

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
