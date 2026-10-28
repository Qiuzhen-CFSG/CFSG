module
public import Theory.GroupAction.SymplecticRankThree.Translations

/-!
# The regular abelian translation group of the reconstructed plane

A collineation fixing the line at infinity and two distinct affine points
is the identity. A translation fixes no affine point unless it is trivial,
and translations in distinct directions commute by the parallelogram rule.
The spatially constructed translations and this rigidity prove closure and
commutativity also for coincident directions. Evaluation at the origin is
therefore an equivalence from the full abelian translation group to the
actual affine plane, and its order is q².

No translation group, additive structure or field action is an input.
All arguments use q≥2, so the same construction covers the binary case.
This proves the additive part of the coordinatization required in Higman
(1964), Lemma 10, pp.153–154. Multiplication and projective field coordinates
remain separate obligations; the group here is not assumed to be the
original source group or a symplectic group.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

/-- The collineations of the base plane fixing its line at infinity pointwise. -/
@[expose] def dilatations : Subgroup (Equiv.Perm (f.Plane hl hq)) where
  carrier := {E | (∀ x y z : f.Plane hl hq,
      (E z : Ω) ∈ D.line (E x) (E y) ↔ (z : Ω) ∈ D.line x y) ∧
    (∀ x : f.Plane hl hq, (x : Ω) ∈ D.block f.infinity → E x = x)}
  one_mem' := ⟨fun _ _ _ => Iff.rfl,fun _ _ => rfl⟩
  mul_mem' {E F} hE hF := ⟨fun x y z => (hE.1 (F x) (F y) (F z)).trans (hF.1 x y z),
    fun x hx => by change E (F x) = x; rw [hF.2 x hx,hE.2 x hx]⟩
  inv_mem' {E} hE := by
    constructor
    · intro x y z
      have hh := hE.1 (E.symm x) (E.symm y) (E.symm z)
      simpa only [Equiv.apply_symm_apply, Equiv.Perm.inv_def] using hh.symm
    · intro x hx
      apply E.injective
      change E (E.symm x) = E x
      rw [Equiv.apply_symm_apply,hE.2 x hx]

abbrev Motion := ↥(f.dilatations hl hq)

namespace Motion
variable {f hl hq}
variable (E : f.Motion hl hq)

theorem collinear (x y z : f.Plane hl hq) :
    (E.val z : Ω) ∈ D.line (E.val x) (E.val y) ↔ (z : Ω) ∈ D.line x y := E.property.1 x y z

theorem infinity_fixed (x : f.Plane hl hq) (hx : (x : Ω) ∈ D.block f.infinity) : E.val x = x :=
  E.property.2 x hx

theorem affine_iff (x : f.Plane hl hq) :
    (E.val x : Ω) ∉ D.block f.infinity ↔ (x : Ω) ∉ D.block f.infinity := by
  constructor
  · intro h hx
    rw [E.infinity_fixed x hx] at h
    exact h hx
  · intro h hx
    have he : E.val x = x := E.val.injective (E.infinity_fixed (E.val x) hx)
    exact h (he ▸ hx)

theorem parallel (d : f.Direction hl hq) (x y : f.Plane hl hq) :
    (E.val y : Ω) ∈ D.line d (E.val x) ↔ (y : Ω) ∈ D.line d x := by
  have hh := E.collinear ⟨d,d.property.2⟩ x y
  rw [E.infinity_fixed ⟨d,d.property.2⟩ d.property.1] at hh
  exact hh

/-- Evaluation on the affine complement; the original projective action is retained. -/
@[expose] def affineEquiv : Equiv.Perm (f.Base hl hq) where
  toFun x := ⟨⟨E.val ⟨x,x.property⟩,(E.affine_iff ⟨x,x.property⟩).mpr x.val.property⟩,
    (E.val ⟨x,x.property⟩).property⟩
  invFun x := ⟨⟨(E⁻¹).val ⟨x,x.property⟩,((E⁻¹).affine_iff ⟨x,x.property⟩).mpr x.val.property⟩,
    ((E⁻¹).val ⟨x,x.property⟩).property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def] using
      congrArg (fun t : f.Plane hl hq => (t : Ω)) (E.val.symm_apply_apply ⟨x,x.property⟩)
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def] using
      congrArg (fun t : f.Plane hl hq => (t : Ω)) (E.val.apply_symm_apply ⟨x,x.property⟩)

/-- A translation has a single direction for all its displacements. -/
def HasDirection (d : f.Direction hl hq) : Prop :=
  ∀ x : f.Plane hl hq, (E.val x : Ω) ∈ D.line d x

def IsTranslation : Prop := ∃ d, E.HasDirection d

theorem direction_spec {d : f.Direction hl hq} (hE : E.HasDirection d)
    (x : f.Plane hl hq) : (E.val x : Ω) ∈ D.line d x := hE x

theorem translation_spec : E.IsTranslation ↔ ∃ d, E.HasDirection d := Iff.rfl

/-- A fixed affine point forces every line through it to be invariant. -/
theorem fixed_point_line {a : f.Plane hl hq} (ha : (a : Ω) ∉ D.block f.infinity)
    (hea : E.val a = a) (x : f.Plane hl hq) : (E.val x : Ω) ∈ D.line a x := by
  by_cases hax : a = x
  · subst x
    rw [hea]
    exact D.left_mem_line _ _
  have hax' : (a : Ω) ≠ x := fun hh => hax (Subtype.ext hh)
  obtain ⟨d,⟨hdl,hdInf⟩,_⟩ := D.existsUnique_line_block hl hq ha hax'
  have hdp : d ∈ D.block (f.level hl hq f.originPoint) :=
    D.line_subset_block a.property x.property hdl
  have hda : d ≠ (a : Ω) := fun he => ha (he ▸ hdInf)
  have he := D.line_eq_of_mem_of_mem hax' hdl (D.left_mem_line _ _) hda
  have hx : (x : Ω) ∈ D.line d a := he.symm ▸ D.right_mem_line _ _
  have hh := (E.parallel ⟨d,hdInf,hdp⟩ a x).mpr hx
  rw [hea] at hh
  exact he ▸ hh

/-- Two fixed affine points force every point off their joining line to be fixed. -/
theorem fixed_off_line {a b : f.Plane hl hq} (hab : (a : Ω) ≠ b)
    (ha : (a : Ω) ∉ D.block f.infinity) (hb : (b : Ω) ∉ D.block f.infinity)
    (hea : E.val a = a) (heb : E.val b = b) (x : f.Plane hl hq)
    (hx : (x : Ω) ∉ D.line a b) : E.val x = x := by
  by_contra hne
  have hxe : (x : Ω) ≠ E.val x := fun he => hne (Subtype.ext he.symm)
  have hax : (a : Ω) ≠ x := fun he => hx (he ▸ D.left_mem_line _ _)
  have hbx : (b : Ω) ≠ x := fun he => hx (he ▸ D.right_mem_line _ _)
  have h₁ := D.line_eq_of_mem_of_mem hax (D.right_mem_line _ _)
    (E.fixed_point_line ha hea x) hxe
  have h₂ := D.line_eq_of_mem_of_mem hbx (D.right_mem_line _ _)
    (E.fixed_point_line hb heb x) hxe
  have he : D.line a x = D.line b x := h₁.symm.trans h₂
  have hba : (b : Ω) ∈ D.line a x := he.symm ▸ D.left_mem_line _ _
  exact hx ((D.line_eq_of_mem hax hba hab) ▸ D.right_mem_line a x)

end Motion

/-- An affine plane of order at least two is not contained in a line. -/
theorem exists_base_off_line (a b : Ω) (hab : a ≠ b) :
    ∃ x : f.Base hl hq, (x : Ω) ∉ D.line a b := by
  by_contra! hh
  have hc : Nat.card (f.Base hl hq) = q*q := by
    rw [Nat.card_congr (f.baseEquiv hl hq),Nat.card_prod,
      (f.axes_card hl hq).1,(f.axes_card hl hq).2.1]
  let g : f.Base hl hq → ↥(D.line a b) := fun x => ⟨x,hh x⟩
  have hg : Function.Injective g := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun t : ↥(D.line a b) => t.val) h))
  have hn := Nat.card_le_card_of_injective g hg
  rw [hc,show Nat.card ↥(D.line a b) = (D.line a b).ncard from rfl,hl a b hab] at hn
  nlinarith

end Theory.GroupAction.SymplecticRankThree.AffineFrame

namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable {f : AffineFrame D}
variable {hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1} {hq : 2 ≤ q}

namespace Motion
variable (E : f.Motion hl hq)

/-- A direction-fixing collineation fixing two different affine points is the identity. -/
theorem eq_one_of_two_fixed {a b : f.Plane hl hq} (hab : (a : Ω) ≠ b)
    (ha : (a : Ω) ∉ D.block f.infinity) (hb : (b : Ω) ∉ D.block f.infinity)
    (hea : E.val a = a) (heb : E.val b = b) : E = 1 := by
  obtain ⟨t,ht⟩ := f.exists_base_off_line hl hq a b hab
  let t' : f.Plane hl hq := ⟨t,t.property⟩
  have het : E.val t' = t' := E.fixed_off_line hab ha hb hea heb t' ht
  have hat : (a : Ω) ≠ t' := fun he => ht (he ▸ D.left_mem_line _ _)
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : (x : Ω) ∉ D.line a b
  · exact E.fixed_off_line hab ha hb hea heb x hx
  by_cases hax : a = x
  · subst x
    exact hea
  have hax' : (a : Ω) ≠ x := fun he => hax (Subtype.ext he)
  have hxt : (x : Ω) ∉ D.line a t' := by
    intro hxt
    have h₁ := D.line_eq_of_mem hab (not_not.mp hx) hax'
    have h₂ := D.line_eq_of_mem hat hxt hax'
    exact ht (h₁ ▸ h₂.symm ▸ D.right_mem_line a t')
  exact E.fixed_off_line hat ha t.val.property hea het x hxt

/-- Two motions agreeing on two different affine points agree everywhere. -/
theorem eq_of_two_images (F : f.Motion hl hq) {a b : f.Plane hl hq}
    (hab : (a : Ω) ≠ b) (ha : (a : Ω) ∉ D.block f.infinity)
    (hb : (b : Ω) ∉ D.block f.infinity)
    (hea : E.val a = F.val a) (heb : E.val b = F.val b) : E = F := by
  symm
  apply inv_mul_eq_one.mp
  apply (F⁻¹ * E).eq_one_of_two_fixed hab ha hb
  · change F.val⁻¹ (E.val a) = a
    rw [hea,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
  · change F.val⁻¹ (E.val b) = b
    rw [heb,Equiv.Perm.inv_def,Equiv.symm_apply_apply]

/-- The affine semiregularity of translations, proved from incidence. -/
theorem HasDirection.eq_one_of_fixed {d : f.Direction hl hq} (hd : E.HasDirection d)
    {a : f.Plane hl hq} (ha : (a : Ω) ∉ D.block f.infinity) (hea : E.val a = a) : E = 1 := by
  have hda : (d : Ω) ≠ a := fun he => ha (he ▸ d.property.1)
  obtain ⟨t,ht⟩ := f.exists_base_off_line hl hq d a hda
  let t' : f.Plane hl hq := ⟨t,t.property⟩
  have het : E.val t' = t' := by
    by_contra hne
    have hte : (t' : Ω) ≠ E.val t' := fun he => hne (Subtype.ext he.symm)
    have hdt : (d : Ω) ≠ t' := f.direction_ne_affine hl hq d t.val
    have hat : (a : Ω) ≠ t' := fun he => ht (he ▸ D.right_mem_line _ _)
    have h₁ := D.line_eq_of_mem_of_mem hdt (D.right_mem_line _ _) (hd t') hte
    have h₂ := D.line_eq_of_mem_of_mem hat (D.right_mem_line _ _)
      (E.fixed_point_line ha hea t') hte
    have he : D.line d t' = D.line a t' := h₁.symm.trans h₂
    have had : (a : Ω) ∈ D.line d t' := he.symm ▸ D.left_mem_line _ _
    exact ht ((D.line_eq_of_mem hdt had hda) ▸ D.right_mem_line d t')
  apply E.eq_one_of_two_fixed (a := a) (b := t') _ ha t.val.property hea het
  exact fun he => ht (he ▸ D.right_mem_line _ _)

theorem IsTranslation.eq_one_of_fixed (ht : E.IsTranslation)
    {a : f.Plane hl hq} (ha : (a : Ω) ∉ D.block f.infinity) (hea : E.val a = a) : E = 1 := by
  obtain ⟨d,hd⟩ := ht
  exact hd.eq_one_of_fixed E ha hea

theorem direction_one (d : f.Direction hl hq) : (1 : f.Motion hl hq).HasDirection d :=
  fun _ => D.right_mem_line _ _

theorem HasDirection.mul {F : f.Motion hl hq} {d : f.Direction hl hq}
    (hE : E.HasDirection d) (hF : F.HasDirection d) : (E*F).HasDirection d := by
  intro x
  by_cases hx : (x : Ω) ∈ D.block f.infinity
  · change (E.val (F.val x) : Ω) ∈ D.line d x
    simp only [F.infinity_fixed x hx,E.infinity_fixed x hx]
    exact D.right_mem_line _ _
  have hdx : (d : Ω) ≠ x := fun he => hx (he ▸ d.property.1)
  have hdFx : (d : Ω) ≠ F.val x :=
    fun he => (F.affine_iff x).mpr hx (he ▸ d.property.1)
  exact (D.line_eq_of_mem hdx (hF x) hdFx) ▸ hE (F.val x)

theorem HasDirection.inv {d : f.Direction hl hq} (hE : E.HasDirection d) :
    (E⁻¹).HasDirection d := by
  intro x
  by_cases hx : (x : Ω) ∈ D.block f.infinity
  · rw [(E⁻¹).infinity_fixed x hx]
    exact D.right_mem_line _ _
  have hdEx : (d : Ω) ≠ (E⁻¹).val x :=
    fun he => ((E⁻¹).affine_iff x).mpr hx (he ▸ d.property.1)
  have hdx : (d : Ω) ≠ x := fun he => hx (he ▸ d.property.1)
  have hh := hE ((E⁻¹).val x)
  change (E.val (E.val⁻¹ x) : Ω) ∈ D.line d ((E⁻¹).val x) at hh
  rw [Equiv.Perm.inv_def,Equiv.apply_symm_apply] at hh
  exact (D.line_eq_of_mem hdEx hh hdx).symm ▸ D.right_mem_line _ _

end Motion

/-- Two different parallel pencils have at most one common affine point. -/
theorem direction_lines_unique {d e : f.Direction hl hq} (hde : (d : Ω) ≠ e)
    {a b x y : Ω} (ha : a ∉ D.block f.infinity) (hb : b ∉ D.block f.infinity)
    (hx : x ∈ D.line d a) (hx' : x ∈ D.line e b)
    (hy : y ∈ D.line d a) (hy' : y ∈ D.line e b) : x = y := by
  by_contra hxy
  have hda : (d : Ω) ≠ a := fun he => ha (he ▸ d.property.1)
  have heb : (e : Ω) ≠ b := fun he => hb (he ▸ e.property.1)
  have hL : D.line d a = D.line e b :=
    (D.line_eq_of_mem_of_mem hda hx hy hxy).symm.trans
      (D.line_eq_of_mem_of_mem heb hx' hy' hxy)
  have hd : (d : Ω) ∈ D.line e b := hL ▸ D.left_mem_line _ _
  exact hde ((D.infinity_on_line e.property.1 hb hd).mp d.property.1)

namespace Motion
variable {E F : f.Motion hl hq}

/-- Translations in different directions commute by the parallelogram rule. -/
theorem HasDirection.commute_of_ne {d e : f.Direction hl hq}
    (hE : E.HasDirection d) (hF : F.HasDirection e) (hde : (d : Ω) ≠ e) : Commute E F := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : (x : Ω) ∈ D.block f.infinity
  · change E.val (F.val x) = F.val (E.val x)
    simp only [F.infinity_fixed x hx,E.infinity_fixed x hx]
  apply Subtype.ext
  apply direction_lines_unique hde ((F.affine_iff x).mpr hx) ((E.affine_iff x).mpr hx)
  · exact hE (F.val x)
  · exact (E.parallel e x (F.val x)).mpr (hF x)
  · exact (F.parallel d x (E.val x)).mpr (hE x)
  · exact hF (E.val x)

/-- A translation is uniquely determined by the image of one affine point. -/
theorem IsTranslation.eq_of_image (hE : E.IsTranslation) (hF : F.IsTranslation)
    {a : f.Plane hl hq} (ha : (a : Ω) ∉ D.block f.infinity)
    (he : E.val a = F.val a) : E = F := by
  obtain ⟨d,hd⟩ := hE
  obtain ⟨e,he'⟩ := hF
  by_cases hde : d = e
  · subst e
    have ht := (hd.inv E).mul (E⁻¹) he'
    have hfix : (E⁻¹*F).val a = a := by
      change E.val⁻¹ (F.val a) = a
      rw [←he,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
    exact inv_mul_eq_one.mp (ht.eq_one_of_fixed (E⁻¹*F) ha hfix)
  · have hde' : (d : Ω) ≠ e := fun hh => hde (Subtype.ext hh)
    have hf : E.val a = a := Subtype.ext (direction_lines_unique hde' ha ha (hd a)
      (he.symm ▸ he' a) (D.right_mem_line _ _) (D.right_mem_line _ _))
    have h₁ := hd.eq_one_of_fixed E ha hf
    have h₂ := he'.eq_one_of_fixed F ha (he.symm.trans hf)
    exact h₁.trans h₂.symm

end Motion
end Theory.GroupAction.SymplecticRankThree.AffineFrame
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

/-- The constructed translations attain every affine point. -/
theorem exists_translation (b : f.Base hl hq) :
    ∃ E : f.Motion hl hq, E.IsTranslation ∧ E.affineEquiv (f.baseOrigin hl hq) = b := by
  obtain ⟨E,hline,hfix,hb,d,hd⟩ := f.plane_translation_exists hl hq b
  exact ⟨⟨E,hline,hfix⟩,⟨d,hd⟩,Subtype.ext (Subtype.ext hb)⟩

namespace Motion
variable {f hl hq} {E F T : f.Motion hl hq}

private theorem eq_of_image_of_commute (hT : T.IsTranslation) (hT1 : T ≠ 1)
    (hE : Commute E T) (hF : Commute F T)
    (he : E.val (f.planeOrigin hl hq) = F.val (f.planeOrigin hl hq)) : E = F := by
  let o := f.planeOrigin hl hq
  have hTo : T.val o ≠ o := fun ht => hT1 (hT.eq_one_of_fixed T f.origin_not_mem ht)
  apply E.eq_of_two_images F (a := o) (b := T.val o)
    (fun hh => hTo (Subtype.ext hh.symm)) f.origin_not_mem
    ((T.affine_iff o).mpr f.origin_not_mem) he
  have h₁ : E.val (T.val o) = T.val (E.val o) :=
    congrArg (fun g : f.Motion hl hq => g.val o) hE.eq
  have h₂ : F.val (T.val o) = T.val (F.val o) :=
    congrArg (fun g : f.Motion hl hq => g.val o) hF.eq
  exact h₁.trans ((congrArg T.val he).trans h₂.symm)

/-- Translations are closed under composition; the proof uses the spatially
constructed translation with the same origin image and two-point rigidity. -/
theorem IsTranslation.mul (hE : E.IsTranslation) (hF : F.IsTranslation) :
    (E*F).IsTranslation := by
  by_cases hE1 : E = 1
  · simpa only [hE1,one_mul] using hF
  by_cases hF1 : F = 1
  · simpa only [hF1,mul_one] using hE
  obtain ⟨d,hd⟩ := hE
  obtain ⟨e,he⟩ := hF
  by_cases hde : d = e
  · subst e
    exact ⟨d,hd.mul E he⟩
  have hde' : (d : Ω) ≠ e := fun hh => hde (Subtype.ext hh)
  have hEF := hd.commute_of_ne he hde'
  obtain ⟨T,hT,hTo⟩ := f.exists_translation hl hq ((E*F).affineEquiv (f.baseOrigin hl hq))
  have hTo' : T.val (f.planeOrigin hl hq) = (E*F).val (f.planeOrigin hl hq) :=
    Subtype.ext (congrArg (fun x : f.Base hl hq => (x : Ω)) hTo)
  obtain ⟨t,ht⟩ := hT
  by_cases htd : t = d
  · have hte : (t : Ω) ≠ e := fun hh => hde (htd.symm.trans (Subtype.ext hh))
    have hTF := ht.commute_of_ne he hte
    have hPF : Commute (E*F) F := hEF.mul_left (Commute.refl F)
    have hEq : T = E*F := eq_of_image_of_commute ⟨e,he⟩ hF1 hTF hPF hTo'
    exact hEq ▸ ⟨t,ht⟩
  · have htd' : (t : Ω) ≠ d := fun hh => htd (Subtype.ext hh)
    have hTE := ht.commute_of_ne hd htd'
    have hPE : Commute (E*F) E := (Commute.refl E).mul_left hEF.symm
    have hEq : T = E*F := eq_of_image_of_commute ⟨d,hd⟩ hE1 hTE hPE hTo'
    exact hEq ▸ ⟨t,ht⟩

theorem IsTranslation.inv (hE : E.IsTranslation) : (E⁻¹).IsTranslation := by
  obtain ⟨d,hd⟩ := hE
  exact ⟨d,hd.inv E⟩

/-- Translations in any directions commute, including the same direction. -/
theorem IsTranslation.commute (hE : E.IsTranslation) (hF : F.IsTranslation) : Commute E F := by
  obtain ⟨d,hd⟩ := hE
  obtain ⟨e,he⟩ := hF
  by_cases hde : d = e
  swap
  · exact hd.commute_of_ne he (fun hh => hde (Subtype.ext hh))
  subst e
  have hdo : (d : Ω) ≠ f.origin := f.direction_ne_affine hl hq d f.originPoint
  obtain ⟨b,hb⟩ := f.exists_base_off_line hl hq d f.origin hdo
  obtain ⟨T,⟨t,ht⟩,hTo⟩ := f.exists_translation hl hq b
  have hTo' : (T.val (f.planeOrigin hl hq) : Ω) = b :=
    congrArg (fun x : f.Base hl hq => (x : Ω)) hTo
  have htd : (t : Ω) ≠ d := by
    intro hh
    have hh' := ht (f.planeOrigin hl hq)
    rw [hh,hTo'] at hh'
    exact hb hh'
  have hET : Commute E T := hd.commute_of_ne ht htd.symm
  obtain ⟨u,hu⟩ := (show F.IsTranslation from ⟨d,he⟩).mul ⟨t,ht⟩
  have hud : (u : Ω) ≠ d := by
    intro hh
    have hdir : (F*T).HasDirection d := (Subtype.ext hh : u=d) ▸ hu
    have hTdir : T.HasDirection d := by
      simpa only [inv_mul_cancel_left] using (he.inv F).mul (F⁻¹) hdir
    exact hb (hTo' ▸ hTdir (f.planeOrigin hl hq))
  have hEP : Commute E (F*T) := hd.commute_of_ne hu hud.symm
  apply mul_right_cancel (b := T)
  calc
    (E*F)*T = E*(F*T) := mul_assoc _ _ _
    _ = (F*T)*E := hEP.eq
    _ = F*(T*E) := mul_assoc _ _ _
    _ = F*(E*T) := by rw [hET.eq]
    _ = (F*E)*T := (mul_assoc _ _ _).symm

end Motion

/-- The full translation group of the reconstructed affine plane. -/
@[expose] def translations : Subgroup (f.Motion hl hq) where
  carrier := {E | E.IsTranslation}
  one_mem' := by
    change ∃ d, (1 : f.Motion hl hq).HasDirection d
    exact ⟨f.directionI hl hq,Motion.direction_one _⟩
  mul_mem' := Motion.IsTranslation.mul
  inv_mem' := Motion.IsTranslation.inv

instance : IsMulCommutative (f.translations hl hq) :=
  ⟨⟨fun E F => Subtype.ext (Motion.IsTranslation.commute E.property F.property).eq⟩⟩

/-- The full translation group acts regularly on the actual affine chart. -/
@[expose] def translationEquiv : f.translations hl hq ≃ f.Base hl hq :=
  Equiv.ofBijective (fun E => E.val.affineEquiv (f.baseOrigin hl hq)) (by
    constructor
    · intro E F he
      apply Subtype.ext
      apply Motion.IsTranslation.eq_of_image E.property F.property (a := f.planeOrigin hl hq)
        f.origin_not_mem
      exact Subtype.ext (congrArg (fun x : f.Base hl hq => (x : Ω)) he)
    · intro b
      obtain ⟨E,hE,hb⟩ := f.exists_translation hl hq b
      exact ⟨⟨E,hE⟩,hb⟩)

/-- The abelian translation group has order q². -/
theorem translations_card : Nat.card (f.translations hl hq) = q^2 := by
  rw [Nat.card_congr (f.translationEquiv hl hq),Nat.card_congr (f.baseEquiv hl hq),
    Nat.card_prod,(f.axes_card hl hq).1,(f.axes_card hl hq).2.1,pow_two]

end Theory.GroupAction.SymplecticRankThree.AffineFrame
