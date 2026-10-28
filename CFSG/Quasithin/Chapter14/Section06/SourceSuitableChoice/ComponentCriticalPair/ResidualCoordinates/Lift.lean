module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.TerminalGeometry
public import Theory.GroupTheory.SectionImageLift

/-!
# Lifting the moving dual plane and the fixed seed factor

The quotient image of [B,R] has order four. Once the central line lies in
this commutator, the section order formula gives an elementary eight-group.
The quotient images of the actual seed commutators lift to generators modulo Z.
A fixed factor C of U/Z is centralized by R, by the two-layer centralizer
lemma. Thus the independent involution is a=u*c; retaining c is essential.

The constructor below is conditional on the explicit quotient image
calculations. It does not assert that those calculations follow from a
natural/dual marking; that finite module calculation remains a separate input.

Source: Aschbacher--Smith, 14.6.22--23 and printed p.1042.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
variable {G : Type*} [Group G] [Finite G]

theorem plane_eq_line_sup_zpowers {V Z : Subgroup G}
    (hV : Nat.card V = 4) (hZ : Nat.card Z = 2) (hZV : Z ≤ V)
    (v : G) (hv : v ∈ V) (hvZ : v ∉ Z) : V = Z ⊔ zpowers v := by
  have hs : Z ⊔ zpowers v ≤ V := sup_le hZV (zpowers_le.mpr hv)
  have hlt : Z < Z ⊔ zpowers v := lt_of_le_of_ne le_sup_left (by
    intro he
    have hv' := (le_sup_right : zpowers v ≤ Z ⊔ zpowers v) (mem_zpowers v)
    rw [←he] at hv'
    exact hvZ hv')
  have hc := card_dvd_of_le hs
  have hc2 : Nat.card Z < Nat.card (Z ⊔ zpowers v : Subgroup G) := by
    have hh := card_le_of_le hlt.le
    exact lt_of_le_of_ne hh (fun he => hlt.ne (eq_of_le_of_card_ge hlt.le he.ge))
  rw [hZ] at hc2
  rw [hV] at hc
  have he : Nat.card (Z ⊔ zpowers v : Subgroup G) = 4 := by
    have hd := Nat.le_of_dvd (by decide : 0 < 4) hc
    have hn : Nat.card (Z ⊔ zpowers v : Subgroup G) ≠ 3 := by
      intro hn
      norm_num [hn] at hc
    omega
  exact (eq_of_le_of_card_ge hs (by rw [he,hV])).symm

omit [Finite G] in
theorem sup_zpowers_eq_of_same_section (Z : Subgroup G) (v t : G)
    (hz : v * t⁻¹ ∈ Z) : Z ⊔ zpowers v = Z ⊔ zpowers t := by
  apply le_antisymm
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have hh := (Z ⊔ zpowers t).mul_mem ((le_sup_left : Z ≤ Z ⊔ zpowers t) hz)
      ((le_sup_right : zpowers t ≤ Z ⊔ zpowers t) (mem_zpowers t))
    simpa using hh
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have hh := (Z ⊔ zpowers v).mul_mem ((le_sup_left : Z ≤ Z ⊔ zpowers v) (Z.inv_mem hz))
      ((le_sup_right : zpowers v ≤ Z ⊔ zpowers v) (mem_zpowers v))
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh

theorem residual_centralizes_fixed_section
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (u : G) (hu : u ∈ D.UH) (C : Subgroup G)
    (hc : ∀ x ∈ D.H, ∀ c ∈ C, ⁅c,x⁆ ∈ D.V₁) :
    (pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype ≤
      centralizer (C : Set G) := by
  let P := h.kernel (zpowers u)
  have hPH : P ≤ D.H := fun x hx =>
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp hx).1
  apply residual_centralizes_of_two_layer P C D.V₁
    (IsPGroup.of_card (p := 2) (n := 1) (by simpa using h.point_card))
    (hPH.trans h.H_centralizes)
  rw [commutator_comm]
  exact commutator_le.mpr (fun c hc' x hx => hc x (hPH hx) c hc')

/-- Lift the moving quotient plane and its actual seed commutators. The fixed
section C is retained in the independent factor a=u*c. -/
noncomputable def residual_span_coordinates_of_section_images
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] (hcard : Nat.card D.V = 4)
    (A B C : Subgroup G) (hAU : A ≤ D.UH) (hBU : B ≤ D.UH) (hCU : C ≤ D.UH)
    (hsep : A ⊓ (B ⊔ C) ≤ D.V₁)
    (hfixed : ∀ x ∈ D.H, ∀ c ∈ C, ⁅c,x⁆ ∈ D.V₁)
    (u b c v : G) (hu : u ∈ A) (huZ : u ∉ D.V₁)
    (hb : b ∈ B) (hc : c ∈ C) (hv : v ∈ D.V) (hvZ : v ∉ D.V₁)
    (hseed : v * (u * b * c)⁻¹ ∈ D.V₁)
    {E : Type*} [Group E] (q : B →* E) (hk : q.ker = D.V₁.subgroupOf B)
    (hn : ((pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype) ≤
      normalizer (B : Set G))
    (hline : D.V₁ ≤ ⁅B,((pResidual 2 (h.kernel (zpowers u))).map
      (h.kernel (zpowers u)).subtype)⁆)
    (himage : Nat.card ((⁅B,((pResidual 2 (h.kernel (zpowers u))).map
      (h.kernel (zpowers u)).subtype)⁆.subgroupOf B).map q) = 4)
    (hbimage : q ⟨b,hb⟩ ∈ (⁅B,((pResidual 2 (h.kernel (zpowers u))).map
      (h.kernel (zpowers u)).subtype)⁆.subgroupOf B).map q)
    (hgenerate : (⁅B,((pResidual 2 (h.kernel (zpowers u))).map
      (h.kernel (zpowers u)).subtype)⁆.subgroupOf B).map q ≤
      ((closure {x : G | ∃ r ∈ ((pResidual 2 (h.kernel (zpowers u))).map
        (h.kernel (zpowers u)).subtype), x = ⁅b,r⁆}).subgroupOf B).map q) :
    SourceResidualSpanCoordinates D.V D.V₁
      ((pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype) := by
  let P := h.kernel (zpowers u)
  let R := (pResidual 2 P).map P.subtype
  let W := ⁅B,R⁆
  have hWB : W ≤ B := le_normalizer_iff_commutator_le_left.mp hn
  have hWU : W ≤ D.UH := hWB.trans hBU
  have hcardW : Nat.card W = 8 := by
    rw [card_eq_section_image_mul_kernel q hk hWB hline, himage, h.point_card]
  have hbW : b ∈ W := mem_of_section_image_mem q hk hline ⟨b,hb⟩ hbimage
  have hgen : W ≤ D.V₁ ⊔ closure {x : G | ∃ r ∈ R, x = ⁅b,r⁆} := by
    apply le_of_section_image_le q hk hWB le_sup_left
    exact hgenerate.trans (map_mono (subgroupOf_mono B le_sup_right))
  have haU : u * c ∈ D.UH := D.UH.mul_mem (hAU hu) (hCU hc)
  have haB : u * c ∉ B := by
    intro hab
    have huBC : u ∈ B ⊔ C := by
      have hh := (B ⊔ C).mul_mem ((le_sup_left : B ≤ B ⊔ C) hab)
        ((le_sup_right : C ≤ B ⊔ C) (C.inv_mem hc))
      simpa only [mul_inv_cancel_right] using hh
    exact huZ (hsep ⟨hu,huBC⟩)
  have haW : u * c ∉ W := fun hh => haB (hWB hh)
  have huR : u ∈ centralizer (R : Set G) := by
    intro r hr
    exact (mem_centralizer_singleton_iff.mp
      (suitable_parabolic_residual_centralizes h u (hAU hu) P le_rfl hr))
  have hcR : c ∈ centralizer (R : Set G) :=
    (le_centralizer_iff.mp (residual_centralizes_fixed_section h u (hAU hu) C hfixed)) hc
  have hcomm : D.UH ≤ centralizer (D.UH : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hbc : b * c = c * b := (hcomm (hCU hc) b (hBU hb))
  have hseed' : D.V = D.V₁ ⊔ zpowers ((u * c) * b) := by
    rw [plane_eq_line_sup_zpowers hcard h.point_card (h.point_lt.le.trans h.plus_le) v hv hvZ,
      sup_zpowers_eq_of_same_section D.V₁ v (u*b*c) hseed]
    rw [mul_assoc u b c, hbc, ←mul_assoc]
  exact {
    W := W
    elementary := IsElementaryAbelian.of_le hWU
    card := hcardW
    a := u*c
    b := b
    order := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ haU)
      (fun he => haW (he ▸ W.one_mem))
    independent := haW
    seed := hseed'
    line := hline
    second := hbW
    normalizes := normalizer_commutator_ge_right B R
    fixed := (centralizer (R : Set G)).mul_mem huR hcR
    commutes := (hcomm.trans (centralizer_le hWU)) haU
    generated := hgen }

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
