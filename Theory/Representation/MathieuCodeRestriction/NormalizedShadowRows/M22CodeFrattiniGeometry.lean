module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeChiefProjection
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.NormalSemisimpleSpan
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Geometry

/-!
# The M22 moved seed in its normal-closure Frattini module

A literal conjugation embedding identifies the displacement span with its
group commutator. If that seed survives the Frattini denominator, its marked
irreducible four-space embeds in the quotient. Normal generation and normality
of the residual image then make the entire Frattini module semisimple on
restriction to the original residual actors. The map retains every actual
seed representative, so it can be used in subsequent chief projections.

Source: Aschbacher--Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement MonoidAlgebra
namespace MathieuCode.NormalizedShadowRows.M22CodeSection
set_option backward.isDefEq.respectTransparency false

private theorem moved_image_commutator
    {A R X : Type*} [Group A] [Group R] [Group X] [IsElementaryAbelian 2 X]
    (σ : Representation (ZMod 2) R (Additive X)) (j : X →* A) (a : R →* A)
    (hj : ∀ r x, j ((σ r (Additive.ofMul x)).toMul) = a r * j x * (a r)⁻¹) :
    (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = ⁅j.range,a.range⁆ := by
  let S := (Coinvariants.ker σ).toAddSubgroup.toSubgroup'
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    have hh : Coinvariants.ker σ ≤ AddSubgroup.toZModSubmodule 2
        ((⁅j.range,a.range⁆).comap j).toAddSubgroup := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨r,x⟩,rfl⟩
      change j ((σ r x-x).toMul) ∈ ⁅j.range,a.range⁆
      change j ((σ r x).toMul / x.toMul) ∈ ⁅j.range,a.range⁆
      have he : j ((σ r x).toMul) = a r * j x.toMul * (a r)⁻¹ := hj r x.toMul
      rw [map_div,he,div_eq_mul_inv]
      rw [commutator_comm]
      exact commutator_mem_commutator ⟨r,rfl⟩ ⟨x.toMul,rfl⟩
    exact hh
  · rw [commutator_comm]
    apply commutator_le.mpr
    rintro _ ⟨r,rfl⟩ _ ⟨x,rfl⟩
    refine ⟨(σ r (Additive.ofMul x)-Additive.ofMul x).toMul,
      Coinvariants.sub_mem_ker _ _,?_⟩
    change j ((σ r (Additive.ofMul x)).toMul / x) = ⁅a r,j x⁆
    rw [map_div,hj,div_eq_mul_inv]
    rfl

private theorem moved_frattini_map
    {A R X : Type*} [Group A] [Finite A] [Group R] [Group X]
    [IsElementaryAbelian 2 X]
    (σ : Representation (ZMod 2) R (Additive X)) (j : X →* A) (a : R →* A)
    (hj : ∀ r x, j ((σ r (Additive.ofMul x)).toMul) = a r * j x * (a r)⁻¹)
    (W : Subgroup A)
    (hW : (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = W)
    (hE : IsPGroup 2 (normalClosure (W : Set A)))
    (hphi : ¬ W ≤ (frattini (normalClosure (W : Set A))).map
      (normalClosure (W : Set A)).subtype) :
    let E := normalClosure (W : Set A)
    letI : Fact (IsPGroup 2 E) := ⟨hE⟩
    letI : IsElementaryAbelian 2 (E ⧸ frattini E) :=
      isElementaryAbelian_quotient_frattini
    let ρ := elementaryRepresentation (p := 2)
      ((quotientAut (frattini E)).comp (MulAut.conjNormal : A →* MulAut E))
    ∃ c : Coinvariants.ker σ →ₗ[ZMod 2] Additive (E ⧸ frattini E),
      c ≠ 0 ∧
      (∀ r (v w : Coinvariants.ker σ), (w : Additive X) = σ r v →
        c w = ρ (a r) (c v)) ∧
      (∀ v, ∃ e : E, (e : A) = j v.val.toMul ∧
        c v = Additive.ofMul (QuotientGroup.mk' (frattini E) e)) ∧
      (∀ w : W, Additive.ofMul (QuotientGroup.mk' (frattini E)
        (inclusion le_normalClosure w)) ∈ LinearMap.range c) := by
  let E := normalClosure (W : Set A)
  let : Fact (IsPGroup 2 E) := ⟨hE⟩
  let : IsElementaryAbelian 2 (E ⧸ frattini E) :=
    isElementaryAbelian_quotient_frattini
  let q := QuotientGroup.mk' (frattini E)
  let ρ := elementaryRepresentation (p := 2)
    ((quotientAut (frattini E)).comp (MulAut.conjNormal : A →* MulAut E))
  have hvW (v : Coinvariants.ker σ) : j v.val.toMul ∈ W := by
    rw [←hW]
    exact ⟨v.val.toMul,v.property,rfl⟩
  let e (v : Coinvariants.ker σ) : E := ⟨j v.val.toMul,le_normalClosure (hvW v)⟩
  let l : Coinvariants.ker σ →+ Additive (E ⧸ frattini E) := {
    toFun v := Additive.ofMul (q (e v))
    map_zero' := by
      change q (e 0) = 1
      have he : e 0 = 1 := by apply Subtype.ext; exact j.map_one
      rw [he,map_one]
    map_add' v w := by
      change q (e (v+w)) = q (e v) * q (e w)
      rw [←map_mul]
      congr 1
      apply Subtype.ext
      exact j.map_mul _ _ }
  let c := l.toZModLinearMap 2
  change ∃ c : Coinvariants.ker σ →ₗ[ZMod 2] Additive (E ⧸ frattini E), _
  refine ⟨c,?_,?_,fun v => ⟨e v,rfl,rfl⟩,?_⟩
  · intro hc
    apply hphi
    intro w hw
    have hw' := hw
    rw [←hW] at hw'
    obtain ⟨v,hv,rfl⟩ := hw'
    let v' : Coinvariants.ker σ := ⟨Additive.ofMul v,hv⟩
    have he : q (e v') = 1 := by
      have hh := LinearMap.congr_fun hc v'
      exact congrArg Additive.toMul hh
    exact ⟨e v',(QuotientGroup.eq_one_iff (e v')).mp he,rfl⟩
  · intro r v w hw
    change q (e w) = (quotientAut (frattini E)) (MulAut.conjNormal (a r)) (q (e v))
    rw [quotientAut_apply_mk]
    congr 1
    apply Subtype.ext
    change j w.val.toMul = a r * j v.val.toMul * (a r)⁻¹
    rw [hw]
    exact hj r v.val.toMul
  · intro w
    have hw : w.val ∈ (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j :=
      hW.ge w.property
    obtain ⟨v,hv,hvw⟩ := hw
    refine ⟨⟨Additive.ofMul v,hv⟩,?_⟩
    change Additive.ofMul (q (e ⟨Additive.ofMul v,hv⟩)) = _
    congr 2
    exact Subtype.ext hvw


private theorem marked_moved_range_irreducible
    {R D X V : Type*} [Group R] [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) R X)
    (r : R →* alternatingGroup (Fin 5)) (hr : Function.Surjective r)
    (e : X ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K)
    (he : ∀ x v, e (σ x v) =
      MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r x) (e v))
    (τ : Representation (ZMod 2) D V) (a : R →* D) (ha : Function.Surjective a)
    (c : Coinvariants.ker σ →ₗ[ZMod 2] V) (hci : Function.Injective c)
    (hc : ∀ x (v w : Coinvariants.ker σ), (w : X) = σ x v → c w = τ (a x) (c v))
    (S : Subrepresentation τ) (hS : S.toSubmodule = c.range) :
    IsIrreducible S.toRepresentation := by
  let M := MathieuCode.NormalizedShadowRows.M22CodeSection.fiveMoved
  obtain ⟨eS,heS⟩ :=
    MathieuCode.NormalizedShadowRows.M22CodeSection.moved_equiv_of_marking σ r hr e he
  have hes (v : M.toSubmodule) : e (eS.symm v) = (v : Additive MathieuCode.M22Quintet.K) := by
    rw [←heS,eS.apply_symm_apply]
  let p : M.toSubmodule →ₗ[ZMod 2] S.toSubmodule :=
    (c.comp eS.symm.toLinearMap).codRestrict S.toSubmodule (fun v => by
      rw [hS]; exact ⟨eS.symm v,rfl⟩)
  have hpi : Function.Injective p := by
    intro v w h
    exact eS.symm.injective (hci (congrArg Subtype.val h))
  have hps : Function.Surjective p := by
    intro w
    have hw : w.val ∈ c.range := hS.le w.property
    obtain ⟨v,hv⟩ := hw
    refine ⟨eS v,?_⟩
    apply Subtype.ext
    change c (eS.symm (eS v)) = w.val
    rw [eS.symm_apply_apply,hv]
  let ep : Representation.Equiv (M.toRepresentation.comp r) (S.toRepresentation.comp a) :=
    .mk (LinearEquiv.ofBijective p ⟨hpi,hps⟩) (by
      intro x
      ext v
      change c (eS.symm (M.toRepresentation (r x) v)) = τ (a x) (c (eS.symm v))
      apply hc x
      apply e.injective
      rw [he,hes,hes]
      rfl)
  have hi : IsIrreducible (M.toRepresentation.comp r) :=
    (irreducible_comp_surjective_iff r hr M.toRepresentation).mpr inferInstance
  exact (irreducible_comp_surjective_iff a ha S.toRepresentation).mp
    ((RepEquiv.ofRepresentationEquiv ep.symm).irreducible_of_euqiv hi)

private theorem normalClosure_frattini_generates
    {A : Type*} [Group A] [Finite A] (W : Subgroup A)
    (hE : IsPGroup 2 (normalClosure (W : Set A))) :
    let E := normalClosure (W : Set A)
    letI : Fact (IsPGroup 2 E) := ⟨hE⟩
    letI : IsElementaryAbelian 2 (E ⧸ frattini E) :=
      isElementaryAbelian_quotient_frattini
    let ρ := elementaryRepresentation (p := 2)
      ((quotientAut (frattini E)).comp (MulAut.conjNormal : A →* MulAut E))
    ∀ S : Subrepresentation ρ,
      (∀ w : W, Additive.ofMul (QuotientGroup.mk' (frattini E)
        (inclusion le_normalClosure w)) ∈ S) → S = ⊤ := by
  let E := normalClosure (W : Set A)
  let : Fact (IsPGroup 2 E) := ⟨hE⟩
  let : IsElementaryAbelian 2 (E ⧸ frattini E) :=
    isElementaryAbelian_quotient_frattini
  let q := QuotientGroup.mk' (frattini E)
  let ρ := elementaryRepresentation (p := 2)
    ((quotientAut (frattini E)).comp (MulAut.conjNormal : A →* MulAut E))
  change ∀ S : Subrepresentation ρ,
    (∀ w : W, Additive.ofMul (q (inclusion le_normalClosure w)) ∈ S) → S = ⊤
  intro S hS
  let F := (S.toSubmodule.toAddSubgroup.toSubgroup'.comap q).map E.subtype
  let : F.Normal := ⟨by
    rintro x ⟨y,hy,rfl⟩ g
    refine ⟨MulAut.conjNormal g y,?_,MulAut.conjNormal_apply g y⟩
    change Additive.ofMul (q (MulAut.conjNormal g y)) ∈ S
    have hm := S.apply_mem_toSubmodule g hy
    change Additive.ofMul
      ((quotientAut (frattini E)) (MulAut.conjNormal g) (q y)) ∈ S at hm
    rw [quotientAut_apply_mk] at hm
    exact hm⟩
  have hWF : W ≤ F := by
    intro w hw
    exact ⟨⟨w,le_normalClosure hw⟩,hS ⟨w,hw⟩,rfl⟩
  have hEF : E ≤ F := normalClosure_le_normal hWF
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro x _
  obtain ⟨e,he⟩ := QuotientGroup.mk'_surjective (frattini E) x.toMul
  obtain ⟨y,hy,hye⟩ := hEF e.property
  have hye' : y = e := Subtype.ext hye
  subst y
  change Additive.ofMul (q e) ∈ S at hy
  change q e = x.toMul at he
  rw [he] at hy
  exact hy


/-- The surviving literal moved seed and its semisimple normal span. -/
@[expose] def M22MovedFrattiniGeometry
    {A R X : Type*} [Group A] [Finite A] [Group R] [Group X]
    [IsElementaryAbelian 2 X]
    (σ : Representation (ZMod 2) R (Additive X)) (j : X →* A) (a : R →* A)
    (W : Subgroup A) (hE : IsPGroup 2 (normalClosure (W : Set A))) : Prop :=
  let E := normalClosure (W : Set A)
  letI : Fact (IsPGroup 2 E) := ⟨hE⟩
  letI : IsElementaryAbelian 2 (E ⧸ frattini E) := isElementaryAbelian_quotient_frattini
  let ρ := elementaryRepresentation (p := 2)
    ((quotientAut (frattini E)).comp (MulAut.conjNormal : A →* MulAut E))
  ∃ c : Coinvariants.ker σ →ₗ[ZMod 2] Additive (E ⧸ frattini E),
    Function.Injective c ∧ Module.finrank (ZMod 2) c.range = 4 ∧ c ≠ 0 ∧
    (∀ r (v w : Coinvariants.ker σ), (w : Additive X) = σ r v →
      c w = ρ (a r) (c v)) ∧
    (∀ v, ∃ e : E, (e : A) = j v.val.toMul ∧
      c v = Additive.ofMul (QuotientGroup.mk' (frattini E) e)) ∧
    (∀ w : W, Additive.ofMul (QuotientGroup.mk' (frattini E)
      (inclusion le_normalClosure w)) ∈ c.range) ∧
    IsSemisimpleModule (ZMod 2)[R] (Representation.asModule (ρ.comp a))

/-- A nonzero marked four-space survives the Frattini quotient of its normal
closure and makes restriction to the original actors semisimple. -/
theorem normalClosure_moved_geometry
    {A R X : Type*} [Group A] [Finite A] [Group R] [Group X]
    [IsElementaryAbelian 2 X]
    (σ : Representation (ZMod 2) R (Additive X))
    (r : R →* alternatingGroup (Fin 5)) (hrs : Function.Surjective r)
    (e : Additive X ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K)
    (he : ∀ x v, e (σ x v) =
      MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r x) (e v))
    (j : X →* A) (a : R →* A)
    (hjσ : ∀ r x, j ((σ r (Additive.ofMul x)).toMul) = a r * j x * (a r)⁻¹)
    (D W : Subgroup A) [D.Normal] (har : a.range = D)
    (hW : (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = W)
    (hE : IsPGroup 2 (normalClosure (W : Set A)))
    (hphi : ¬ W ≤ (frattini (normalClosure (W : Set A))).map
      (normalClosure (W : Set A)).subtype) :
    M22MovedFrattiniGeometry σ j a W hE := by
  let E := normalClosure (W : Set A)
  let : Fact (IsPGroup 2 E) := ⟨hE⟩
  let : IsElementaryAbelian 2 (E ⧸ frattini E) := isElementaryAbelian_quotient_frattini
  let ρ := elementaryRepresentation (p := 2)
    ((quotientAut (frattini E)).comp (MulAut.conjNormal : A →* MulAut E))
  obtain ⟨c,hcn,hc,hcq,hcr⟩ := moved_frattini_map σ j a hjσ W hW hE hphi
  obtain ⟨hci,hcd⟩ :=
    MathieuCode.NormalizedShadowRows.M22CodeSection.moved_projection_of_marking
      σ r hrs e he (ρ.comp a) c hc hcn
  change ∃ c : Coinvariants.ker σ →ₗ[ZMod 2] Additive (E ⧸ frattini E), _
  refine ⟨c,hci,hcd,hcn,hc,hcq,hcr,?_⟩
  let a' : R →* D := a.codRestrict D (fun r => har.le ⟨r,rfl⟩)
  have has : Function.Surjective a' := by
    intro d
    obtain ⟨r,hr⟩ := har.ge d.property
    exact ⟨r,Subtype.ext hr⟩
  let S : Subrepresentation (ρ.comp D.subtype) := {
    toSubmodule := c.range
    apply_mem_toSubmodule d v hv := by
      obtain ⟨r,rfl⟩ := has d
      obtain ⟨w,rfl⟩ := hv
      have hw : σ r w ∈ Coinvariants.ker σ := by
        simpa only [sub_add_cancel] using
          (Coinvariants.ker σ).add_mem (Coinvariants.sub_mem_ker r w.val) w.property
      exact ⟨⟨σ r w,hw⟩,hc r w ⟨σ r w,hw⟩ rfl⟩ }
  have hi : IsIrreducible S.toRepresentation :=
    marked_moved_range_irreducible σ r hrs e he (ρ.comp D.subtype) a' has c hci hc S rfl
  have hss : IsSemisimpleModule (ZMod 2)[D] S.asSubmodule := by
    let := Representation.BinaryOffender.Homogeneous.simple_asSubmodule S hi
    infer_instance
  have hsemi : IsSemisimpleModule (ZMod 2)[D] (Representation.asModule (ρ.comp D.subtype)) :=
    normal_restriction_semisimple_of_generating_family ρ D (fun _ : Unit => S)
      (fun _ => hss) (by
        intro T hT
        apply normalClosure_frattini_generates W hE T
        intro w
        exact hT () (hcr w))
  exact (semisimple_comp_iff_of_surjective (ρ.comp D.subtype) a' has).mpr hsemi

end MathieuCode.NormalizedShadowRows.M22CodeSection
