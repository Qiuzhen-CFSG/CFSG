module
public import Theory.SpecificGroups.G2.TernaryCoreActions
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Full ternary parabolic representations on the literal radical quotients

The cubic kernels in TernaryCoreCoordinates are the exact derived subgroups.
Thus every endpoint conjugation acts on the concrete four-dimensional
quotient. The whole quotient square commutes, and the two actual generator
values agree with the Weyl and simple-root formulas. Actors centralizing
the distinguished torus involution preserve the canonical lifted section.

These full actions are the model targets for AtlasCoreComparison in the
I.4.5 construction (Aschbacher–Smith, printed p.417). The root calculations
retain the imported ATLAS attribution and LICENSES/ATLAS.txt.
-/

@[expose] public section
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.Explicit Atlas.SplitOctonion
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Atlas.G2.TernaryCore

private theorem quotient_transport {D W : Type*} [Group D] [Group W]
    (q : D →* W) [q.ker.Characteristic] (e : (D ⧸ q.ker) ≃* W)
    (he : ∀ x,e (QuotientGroup.mk' q.ker x)=q x) (a : MulAut D) (x : D) :
    MulAut.congr e (quotientAut q.ker a) (q x)=q (a x) := by
  have h : e.symm (q x)=QuotientGroup.mk' q.ker x := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply,he]
  change e (quotientAut q.ker a (e.symm (q x)))=_
  rw [h,quotientAut_apply_mk,he]

/-- The cubic kernel is precisely the derived subgroup, not a larger center. -/
theorem shortKernel_eq_commutator : shortQuotient.ker=_root_.commutator (radical₁ (F:=ZMod 3)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨k,v,rfl⟩ := short_surjective x
    have hv : v=1 := (shortQuotient_apply k v).symm.trans hx
    subst v
    have h := shortExtension_commutator
      (Multiplicative.ofAdd ![k,0,0,0]) (Multiplicative.ofAdd ![0,0,0,1])
    have he : shortForm (Multiplicative.ofAdd ![k,0,0,0]) (Multiplicative.ofAdd ![0,0,0,1])=k := by
      simp [shortForm]
    rw [he] at h
    rw [←h]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  · apply commutator_le.mpr
    intro x _ y _
    rw [MonoidHom.mem_ker,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

instance shortKernel_characteristic : shortQuotient.ker.Characteristic := by
  rw [shortKernel_eq_commutator]
  infer_instance

/-- Actual conjugation by every element of the whole Atlas endpoint. -/
def shortCoreAction : parabolic₁ (F:=ZMod 3) →* MulAut (radical₁ (F:=ZMod 3)) :=
  radical₁.normalizerMonoidHom.comp (inclusion short_parabolic_normalizes)

/-- The first isomorphism theorem with the explicit root-coordinate section. -/
def shortAbelianizationEquiv : (radical₁ (F:=ZMod 3) ⧸ shortQuotient.ker) ≃* V :=
  QuotientGroup.quotientKerEquivOfRightInverse shortQuotient (short 0) (shortQuotient_apply 0)

@[simp] theorem shortAbelianizationEquiv_mk (x : radical₁ (F:=ZMod 3)) :
    shortAbelianizationEquiv (QuotientGroup.mk' shortQuotient.ker x)=shortQuotient x := rfl

/-- The full endpoint action on the concrete four-dimensional module. -/
def shortQuotientAction : parabolic₁ (F:=ZMod 3) →* MulAut V :=
  (MulAut.congr shortAbelianizationEquiv).toMonoidHom.comp
    ((quotientAut shortQuotient.ker).comp shortCoreAction)

/-- The quotient square commutes for every endpoint element and every core element. -/
theorem shortQuotientAction_quotient (a : parabolic₁ (F:=ZMod 3)) (x : radical₁ (F:=ZMod 3)) :
    shortQuotientAction a (shortQuotient x)=shortQuotient (shortCoreAction a x) :=
  quotient_transport shortQuotient shortAbelianizationEquiv shortAbelianizationEquiv_mk (shortCoreAction a) x

/-- The cubic kernel is precisely the derived subgroup, not a larger center. -/
theorem longKernel_eq_commutator : longQuotient.ker=_root_.commutator (radical₂ (F:=ZMod 3)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨k,v,rfl⟩ := long_surjective x
    have hv : v=1 := (longQuotient_apply k v).symm.trans hx
    subst v
    have h := longExtension_commutator
      (Multiplicative.ofAdd ![0,0,0,k]) (Multiplicative.ofAdd ![0,0,1,0])
    have he : longForm (Multiplicative.ofAdd ![0,0,0,k]) (Multiplicative.ofAdd ![0,0,1,0])=k := by
      simp [longForm]
    rw [he] at h
    rw [←h]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  · apply commutator_le.mpr
    intro x _ y _
    rw [MonoidHom.mem_ker,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

instance longKernel_characteristic : longQuotient.ker.Characteristic := by
  rw [longKernel_eq_commutator]
  infer_instance

/-- Actual conjugation by every element of the whole Atlas endpoint. -/
def longCoreAction : parabolic₂ (F:=ZMod 3) →* MulAut (radical₂ (F:=ZMod 3)) :=
  radical₂.normalizerMonoidHom.comp (inclusion long_parabolic_normalizes)

/-- The first isomorphism theorem with the explicit root-coordinate section. -/
def longAbelianizationEquiv : (radical₂ (F:=ZMod 3) ⧸ longQuotient.ker) ≃* V :=
  QuotientGroup.quotientKerEquivOfRightInverse longQuotient (long 0) (longQuotient_apply 0)

@[simp] theorem longAbelianizationEquiv_mk (x : radical₂ (F:=ZMod 3)) :
    longAbelianizationEquiv (QuotientGroup.mk' longQuotient.ker x)=longQuotient x := rfl

/-- The full endpoint action on the concrete four-dimensional module. -/
def longQuotientAction : parabolic₂ (F:=ZMod 3) →* MulAut V :=
  (MulAut.congr longAbelianizationEquiv).toMonoidHom.comp
    ((quotientAut longQuotient.ker).comp longCoreAction)

/-- The quotient square commutes for every endpoint element and every core element. -/
theorem longQuotientAction_quotient (a : parabolic₂ (F:=ZMod 3)) (x : radical₂ (F:=ZMod 3)) :
    longQuotientAction a (longQuotient x)=longQuotient (longCoreAction a x) :=
  quotient_transport longQuotient longAbelianizationEquiv longAbelianizationEquiv_mk (longCoreAction a) x

/-- The full quotient representation has the computed Weyl matrix. -/
theorem shortQuotientAction_weyl (v : V) :
    shortQuotientAction ⟨weylS,mem_sup_right (subset_closure (by simp))⟩ v=shortWeyl v := by
  rw [←shortQuotient_apply 0 v,shortQuotientAction_quotient]
  have h : shortCoreAction ⟨weylS,mem_sup_right (subset_closure (by simp))⟩ (short 0 v)=
      short 0 (shortWeyl v) := by
    apply Subtype.ext
    exact (short_weyl 0 v).trans (by rw [neg_zero])
  simp only [h,shortQuotient_apply]

/-- The full quotient representation has the computed simple-root matrix. -/
theorem shortQuotientAction_root (v : V) :
    shortQuotientAction ⟨rootF 1,mem_sup_left (mem_sup_left (subset_closure (by simp)))⟩ v=shortRoot v := by
  rw [←shortQuotient_apply 0 v,shortQuotientAction_quotient]
  have h : shortCoreAction ⟨rootF 1,mem_sup_left (mem_sup_left (subset_closure (by simp)))⟩ (short 0 v)=short 0 (shortRoot v) := by
    apply Subtype.ext
    exact short_root 0 v
  simp only [h,shortQuotient_apply]

/-- Actors centralizing the distinguished torus involution preserve the canonical section. -/
theorem shortCoreAction_involution (a : parabolic₁ (F:=ZMod 3))
    (ha : Commute (a:Model (ZMod 3)) (torus (-1) (-1))) (x : radical₁ (F:=ZMod 3)) :
    shortCoreAction a (shortInvolution x)=shortInvolution (shortCoreAction a x) := by
  apply Subtype.ext
  change (a:Model (ZMod 3))*(shortInvolution x:Model (ZMod 3))*(a:Model (ZMod 3))⁻¹=_
  rw [shortInvolution_ambient,shortInvolution_ambient]
  change (a:Model (ZMod 3))*(torus (-1) (-1)*(x:Model (ZMod 3))*(torus (-1) (-1))⁻¹)*
    (a:Model (ZMod 3))⁻¹=torus (-1) (-1)*((a:Model (ZMod 3))*(x:Model (ZMod 3))*
      (a:Model (ZMod 3))⁻¹)*(torus (-1) (-1))⁻¹
  calc
    _=((a:Model (ZMod 3))*torus (-1) (-1))*(x:Model (ZMod 3))*
      ((a:Model (ZMod 3))*torus (-1) (-1))⁻¹ := by group
    _=(torus (-1) (-1)*(a:Model (ZMod 3)))*(x:Model (ZMod 3))*
      (torus (-1) (-1)*(a:Model (ZMod 3)))⁻¹ := by rw [ha.eq]
    _=_ := by group

/-- The full quotient representation has the computed Weyl matrix. -/
theorem longQuotientAction_weyl (v : V) :
    longQuotientAction ⟨weylR,mem_sup_right (subset_closure (by simp))⟩ v=longWeyl v := by
  rw [←longQuotient_apply 0 v,longQuotientAction_quotient]
  have h : longCoreAction ⟨weylR,mem_sup_right (subset_closure (by simp))⟩ (long 0 v)=
      long 0 (longWeyl v) := by
    apply Subtype.ext
    exact (long_weyl 0 v).trans (by rw [neg_zero])
  simp only [h,longQuotient_apply]

/-- The full quotient representation has the computed simple-root matrix. -/
theorem longQuotientAction_root (v : V) :
    longQuotientAction ⟨rootE 1,mem_sup_left (mem_sup_left (subset_closure (by simp)))⟩ v=longRoot v := by
  rw [←longQuotient_apply 0 v,longQuotientAction_quotient]
  have h : longCoreAction ⟨rootE 1,mem_sup_left (mem_sup_left (subset_closure (by simp)))⟩ (long 0 v)=long 0 (longRoot v) := by
    apply Subtype.ext
    exact long_root 0 v
  simp only [h,longQuotient_apply]

/-- Actors centralizing the distinguished torus involution preserve the canonical section. -/
theorem longCoreAction_involution (a : parabolic₂ (F:=ZMod 3))
    (ha : Commute (a:Model (ZMod 3)) (torus 1 (-1))) (x : radical₂ (F:=ZMod 3)) :
    longCoreAction a (longInvolution x)=longInvolution (longCoreAction a x) := by
  apply Subtype.ext
  change (a:Model (ZMod 3))*(longInvolution x:Model (ZMod 3))*(a:Model (ZMod 3))⁻¹=_
  rw [longInvolution_ambient,longInvolution_ambient]
  change (a:Model (ZMod 3))*(torus 1 (-1)*(x:Model (ZMod 3))*(torus 1 (-1))⁻¹)*
    (a:Model (ZMod 3))⁻¹=torus 1 (-1)*((a:Model (ZMod 3))*(x:Model (ZMod 3))*
      (a:Model (ZMod 3))⁻¹)*(torus 1 (-1))⁻¹
  calc
    _=((a:Model (ZMod 3))*torus 1 (-1))*(x:Model (ZMod 3))*
      ((a:Model (ZMod 3))*torus 1 (-1))⁻¹ := by group
    _=(torus 1 (-1)*(a:Model (ZMod 3)))*(x:Model (ZMod 3))*
      (torus 1 (-1)*(a:Model (ZMod 3)))⁻¹ := by rw [ha.eq]
    _=_ := by group

end Atlas.G2.TernaryCore
