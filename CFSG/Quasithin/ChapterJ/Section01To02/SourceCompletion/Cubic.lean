module

public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Local
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicCompletion
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension

/-!
# The opening cubic-centralizer argument from Ru1/Ru2

The actual quaternion and outer involution construct marked semidihedral
rotation and reflection generators. Their embedded image is a Sylow subgroup
of the original local centralizer, with its half-turn equal to z. Separately,
Sylow conjugacy and the source inverter of B give H-control of cubic-generator
fusion. Thus the proved I.4.1 theorem applies to the original C_G(B)/B without
extra Sylow, marking, or fusion assumptions.

Source: Aschbacher–Smith, J.2.7(2),(9), printed p.435.
-/

public section
noncomputable section

open Subgroup
namespace CFSG.Quasithin.ChapterJ.SourceCompletion
private theorem marked_embedding {G : Type*} [Group G] [Finite G]
    (a b : G) (ha : orderOf a = 8) (hb : b ^ 2 = 1) (hab : b*a*b⁻¹=a^3) :
    ∃ f : Semidihedral.StandardModel 4 (Nat.le_refl 4) →* G,
      Function.Injective f ∧
      f (Semidihedral.standardRotation 4 (Nat.le_refl 4)) = a ∧
      f (Semidihedral.standardReflection 4 (Nat.le_refl 4)) = b := by
  obtain ⟨f, hfa, hfb⟩ := Semidihedral.standardModel_hom_of_relations
    (Nat.le_refl 4) a b (show a ^ 8 = 1 from ha ▸ pow_orderOf_eq_one a) hb hab
  let aR : f.range := ⟨a, ⟨_, hfa⟩⟩
  let bR : f.range := ⟨b, ⟨_, hfb⟩⟩
  obtain ⟨e⟩ := Semidihedral.equiv_of_small_twisted_generators aR bR
    ((Subgroup.orderOf_coe aR).symm.trans ha) (Subtype.ext hb) (Subtype.ext hab)
    (by calc Nat.card f.range ≤ Nat.card (Semidihedral.StandardModel 4 (Nat.le_refl 4)) :=
               Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective
             _ = 16 := Semidihedral.standardModel_card 4 (Nat.le_refl 4))
  have hbij := f.rangeRestrict_surjective.bijective_of_nat_card_le
    (show Nat.card (Semidihedral.StandardModel 4 (Nat.le_refl 4)) ≤ Nat.card f.range from
      (Nat.card_congr e.toEquiv).symm.le)
  refine ⟨f, ?_, hfa, hfb⟩
  intro x y h
  exact hbij.1 (Subtype.ext h)
end CFSG.Quasithin.ChapterJ.SourceCompletion

namespace CFSG.Quasithin.ChapterJ.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Centralizers.Choices d)
theorem source_sylowThree_H : ∃ P : Sylow 3 d.toTypeRuSetup.H,
    (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B := by
  have hp := ((c.sylowThree.isPGroup').map d.toTypeRuSetup.L₁.subtype).comap_subtype
    (K := d.toTypeRuSetup.H)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hc : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, d.ru2.card_H d.card_Z]
    decide +kernel
  have he : c.B.subgroupOf d.toTypeRuSetup.H = (P : Subgroup d.toTypeRuSetup.H) :=
    eq_of_le_of_card_ge hP (by
      rw [Nat.card_congr (subgroupOfEquivOfLe c.B_le_H).toEquiv, B_card c, hc])
  exact ⟨P, he ▸ map_subgroupOf_eq_of_le c.B_le_H⟩
end CFSG.Quasithin.ChapterJ.SourceCompletion

namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)
private def localEquiv : Fusion.CB d.toTypeRuSetup c.sylowThree ≃*
    centralizer ({c.zInGB} : Set c.GB) where
  toFun x := ⟨⟨x, x.property.2⟩, by rw [c.localCentralizer_eq]; exact x.property.1⟩
  invFun x := ⟨x, by
    have hx := x.property
    have hxH : (x.val : G) ∈ d.toTypeRuSetup.H := c.localCentralizer_eq.le hx
    exact ⟨hxH, x.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem local_card : Nat.card (centralizer ({c.zInGB} : Set c.GB)) = 48 := by
  rw [← Nat.card_congr (localEquiv c).toEquiv]
  obtain ⟨e⟩ := (fusion c).2.1.2.2
  rw [card_eq_card_quotient_mul_card_subgroup
    ((Fusion.BSubgroup d.toTypeRuSetup c.sylowThree).subgroupOf
      (Fusion.CB d.toTypeRuSetup c.sylowThree)), Nat.card_congr e.toEquiv,
    Semidihedral.standardModel_card,
    Nat.card_congr (subgroupOfEquivOfLe (fusion c).2.1.1).toEquiv]
  change 16 * Nat.card c.B = 48
  rw [B_card c]

/-- The marked SD16 Sylow used in J.2.7 is constructed from the original setup. -/
theorem cubicLocalTwo : Nonempty (CubicLocalTwo c) := by
  let cp := Fusion.centralProductData_of_quaternion d c.sylowThree
    (quaternion c.sylowThree)
  obtain ⟨i, hiK, hi⟩ := Fusion.Outer.exists_cubic_centralizing_involution_of_count
    d.toTypeRuSetup c.sylowThree (fusion c).2.2.1.1.2.1
  have hz1 : c.z ≠ 1 := by
    intro h
    have hz := z_order c
    simp [h] at hz
  obtain ⟨a, ha, hrel, haz, _⟩ := Fusion.Outer.quaternion_rotation d c.sylowThree
    cp c.z_mem_Z hz1 i hiK hi
  let E := localEquiv c
  obtain ⟨f, hf, hfa, hfi⟩ := marked_embedding (E a) (E i)
    ((E.orderOf_eq a).trans ((Subgroup.orderOf_coe a).symm.trans ha))
    (by
      have h : i ^ 2 = 1 := Subtype.ext (hi ▸ pow_orderOf_eq_one (i : G))
      simpa only [map_pow, map_one] using congrArg E h)
    (by
      have h : i * a * i⁻¹ = a ^ 3 := Subtype.ext hrel
      simpa only [map_mul, map_inv, map_pow] using congrArg E h)
  have hc : Nat.card f.range = 16 := by
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans
      (Semidihedral.standardModel_card 4 (Nat.le_refl 4))
  obtain ⟨P, hP⟩ := (IsPGroup.of_card (p := 2) (n := 4) hc).exists_le_sylow
  have hPc : Nat.card P = 16 := by
    rw [P.card_eq_multiplicity, local_card c]
    decide +kernel
  have hPe : f.range = (P : Subgroup (centralizer ({c.zInGB} : Set c.GB))) :=
    eq_of_le_of_card_ge hP (by rw [hc, hPc])
  let g := (centralizer ({c.zInGB} : Set c.GB)).subtype.comp f
  have hg : Function.Injective g := Subtype.val_injective.comp hf
  have hr : g.range = (P : Subgroup (centralizer ({c.zInGB} : Set c.GB))).map
      (centralizer ({c.zInGB} : Set c.GB)).subtype := by
    rw [MonoidHom.range_comp, hPe]
  let e := (MonoidHom.ofInjective hg).trans (MulEquiv.subgroupCongr hr)
  refine ⟨{P := P, marking := e.symm, central_marking := ?_, reflection_outside := ?_}⟩
  · change g (Semidihedral.standardRotation 4 (Nat.le_refl 4) ^ 4) = c.zInGB
    rw [map_pow]
    change ((f (Semidihedral.standardRotation 4 (Nat.le_refl 4))) : c.GB) ^ 4 = c.zInGB
    rw [hfa]
    exact Subtype.ext haz
  · change (((g (Semidihedral.standardReflection 4 (Nat.le_refl 4))) : c.GB) : G) ∉
      d.toTypeRuSetup.K
    change (((f (Semidihedral.standardReflection 4 (Nat.le_refl 4))) : c.GB) : G) ∉ _
    rw [hfi]
    exact hiK
end CFSG.Quasithin.ChapterJ.SourceCompletion

namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)
omit [Finite G] in
private theorem inverse_cubic (a : G) (ha : a ^ 3 = 1) : a ^ 2 = a⁻¹ := by
  apply mul_right_cancel (b := a)
  rw [← pow_succ, ha, inv_mul_cancel]

/-- The original H has one class of elements of order three, meeting the chosen B. -/
theorem cubic_generator_control : ∃ b : G, c.B = zpowers b ∧
    ∀ x : G, x ∈ d.toTypeRuSetup.H → orderOf x = 3 →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b := by
  obtain ⟨P, hP⟩ := source_sylowThree_H c
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := c.B) 3 (by rw [B_card c])
  have hbG : orderOf (b : G) = 3 := (Subgroup.orderOf_coe b).trans hb
  have hgen : c.B = zpowers (b : G) :=
    (eq_of_le_of_card_ge (zpowers_le.mpr b.property) (by
      rw [Nat.card_zpowers, hbG, B_card c])).symm
  have htransport := c.inverterTransport_source P hP
  have hsH : c.s ∈ d.toTypeRuSetup.H := d.S_le_H c.s_mem.1
  have hsKQ := c.s_conjugate_mem_K_sdiff_Q (fusion c).2.2.1 hsH (IsConj.refl c.s)
  obtain ⟨k, hk, hki⟩ := htransport c.s hsKQ.1 hsKQ.2 c.s_order_source
  let v : d.toTypeRuSetup.H := ⟨k*c.s*k⁻¹,
    d.toTypeRuSetup.H.mul_mem (d.toTypeRuSetup.H.mul_mem hk hsH)
      (d.toTypeRuSetup.H.inv_mem hk)⟩
  have hv : (v : G) * (b : G) * (v : G)⁻¹ = (b : G)⁻¹ := hki b b.property
  refine ⟨b, hgen, ?_⟩
  intro x hxH hx3
  obtain ⟨y, hxy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow
    (x := (⟨x, hxH⟩ : d.toTypeRuSetup.H)) (n := 1)
    (by rw [← Subgroup.orderOf_coe, hx3]; rfl)
  have hyB : ((y : d.toTypeRuSetup.H) : G) ∈ c.B := by
    rw [← hP]
    exact mem_map_of_mem d.toTypeRuSetup.H.subtype y.property
  let yB : c.B := ⟨y, hyB⟩
  have hbne : b ≠ 1 := by intro h; simp [h] at hb
  obtain ⟨n, hn⟩ := mem_powers_of_prime_card (B_card c) hbne (g' := yB)
  obtain ⟨h, hh⟩ := isConj_iff.mp hxy
  have hhe : (h : G) * x * (h : G)⁻¹ = (b : G) ^ (n % 3) := by
    have he := congrArg (fun a : d.toTypeRuSetup.H => (a : G)) hh
    change (h : G) * x * (h : G)⁻¹ = ((y : d.toTypeRuSetup.H) : G) at he
    rw [← congrArg (fun a : c.B => (a : G)) hn] at he
    exact he.trans (pow_eq_pow_mod n (hbG ▸ pow_orderOf_eq_one (b : G)))
  have hnlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
  have hnzero : n % 3 ≠ 0 := by
    intro hn0
    have hx1 : x = 1 := by
      apply (MulAut.conj (h : G)).injective
      simpa only [MulAut.conj_apply, map_one, hn0, pow_zero] using hhe
    simp [hx1] at hx3
  interval_cases hm : n % 3
  · exact (hnzero rfl).elim
  · exact ⟨h, by simpa only [hm, pow_one] using hhe⟩
  · refine ⟨v⁻¹ * h, ?_⟩
    change ((v : G)⁻¹ * h) * x * ((v : G)⁻¹ * h)⁻¹ = b
    rw [inverse_cubic (b : G) (hbG ▸ pow_orderOf_eq_one (b : G))] at hhe
    calc
      _ = (v : G)⁻¹ * ((h : G)*x*(h : G)⁻¹) * v := by group
      _ = (v : G)⁻¹ * (b : G)⁻¹ * v := by rw [hhe]
      _ = b := by rw [← hv]; group
end CFSG.Quasithin.ChapterJ.SourceCompletion

namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The A.1.7 fusion premise follows from the stronger single cubic H-class. -/
theorem cubic_generator_fusion : ∃ b : G, c.B = zpowers b ∧
    ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b := by
  obtain ⟨b, hb, hcontrol⟩ := cubic_generator_control c
  refine ⟨b, hb, fun x hx hbx => hcontrol x hx ?_⟩
  have hb3 : orderOf b = 3 := by rw [← Nat.card_zpowers, ← hb, B_card c]
  obtain ⟨g, hg⟩ := isConj_iff.mp hbx
  rw [← hg]
  exact ((MulAut.conj g).orderOf_eq b).trans hb3

/-- J.2.7(2), including the image of the actual two-residual. -/
theorem cubic_quotient : ∃ e : c.CubicQuotient ≃* AlternatingSix.M10.extension,
    (pResidual 2 c.CubicQuotient).map e.toMonoidHom =
      AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension := by
  obtain ⟨t⟩ := cubicLocalTwo c
  obtain ⟨b, hb, hcontrol⟩ := cubic_generator_fusion c
  exact c.quotient_marked_M10_recognition_of_source (B_card c) t
    (fusion c).2.1 (fusion c).2.2.1 b hb hcontrol

/-- J.2.7(9) on the literal ambient centralizer. -/
theorem cubic_involutions (i : G) (hi : i ∈ c.GB) (hi2 : orderOf i = 2) :
    IsConj i c.z := by
  obtain ⟨t⟩ := cubicLocalTwo c
  exact t.involutions_GB_fused (fusion c).2.2.1 i hi hi2

/-- The exact cubic-centralizer order before the triple-cover identification. -/
theorem GB_card : Nat.card c.GB = 2160 := by
  obtain ⟨e, _⟩ := cubic_quotient c
  exact c.GB_card_of_M10 (B_card c) e

/-- An original s-conjugate in H inverts the specified cubic subgroup. -/
theorem exists_inverter : ∃ h ∈ d.toTypeRuSetup.H,
    c.InvertsB (h*c.s*h⁻¹) ∧ orderOf (h*c.s*h⁻¹) = 2 := by
  obtain ⟨P, hP⟩ := source_sylowThree_H c
  exact c.exists_s_inverting_H_conjugate_of_transport (fusion c).2.2.1
    (c.inverterTransport_source P hP)

/-- The original normalizer quotient has the required order 1440. -/
theorem normalizer_quotient_card : Nat.card c.NormalizerQuotient = 1440 := by
  obtain ⟨t⟩ := cubicLocalTwo c
  obtain ⟨b, hb, hcontrol⟩ := cubic_generator_fusion c
  obtain ⟨h, _, hv, hv2⟩ := exists_inverter c
  exact c.normalizerQuotient_card_of_source_inverter (B_card c) t
    (fusion c).2.1 (fusion c).2.2.1 b hb hcontrol _ hv hv2

end CFSG.Quasithin.ChapterJ.SourceCompletion
