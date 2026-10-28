module
public import Theory.Representation.QuaternionSixteenTernary.Frame
public import Theory.Representation.QuaternionSixteenTernary.Conjugacy

/-!
# Simultaneous coordinates for the marked ternary complement action

An actual Q₁₆ action on a ternary space of order81 first supplies the fixed
quaternion frame. The checked cubic classification then aligns its nontrivial
normalizing cubic while preserving the reflection and quaternion subgroup.
The alternating-form calculation gives a single nonzero scalar, proving
uniqueness of the resulting marked similitude action.

Source: Aschbacher, *Sporadic Groups* (1994), 45.11, p.248.
-/

public section
namespace Theory.Representation.QuaternionSixteenTernary
variable {U : Type*} [AddCommGroup U] [Module (ZMod 3) U]

@[expose] def quaternionWord (A R : U → U) (k : Fin 8) (v : U) : U :=
  ![v,-v,A (A v),-A (A v),A (R v),-A (R v),
    A (A (A (R v))),-A (A (A (R v)))] k

/-- The original Q₁₆ generators and the nontrivial cubic normalizing its Q₈. -/
structure MarkedAction (U : Type*) [AddCommGroup U] [Module (ZMod 3) U] where
  rotation : U ≃ₗ[ZMod 3] U
  reflection : U ≃ₗ[ZMod 3] U
  cubic : U ≃ₗ[ZMod 3] U
  quaternion : Relations rotation reflection
  cubic_cube : ∀ v, cubic (cubic (cubic v))=v
  inverts_cubic : ∀ v, reflection (cubic v)=cubic (cubic (reflection v))
  cubic_nontrivial : ∃ v, cubic v≠v
  normalizes : ∀ k : Fin 8, ∃ j : Fin 8, ∀ v,
    cubic (quaternionWord rotation reflection k v)=quaternionWord rotation reflection j (cubic v)

private def tupleCoordinates : V ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) where
  toFun x := ![x.1,x.2.1,x.2.2.1,x.2.2.2]
  invFun x := (x 0,x 1,x 2,x 3)
  left_inv x := by rfl
  right_inv x := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' t x := by funext i; fin_cases i <;> rfl

private theorem tupleCoordinates_apply (x : V) :
    tupleCoordinates x=![x.1,x.2.1,x.2.2.1,x.2.2.2] := rfl

namespace MarkedAction
variable (M : MarkedAction U)

/-- A Q₁₆ action of order81 has the fixed quaternion/reflection matrices. -/
theorem exists_quaternion_coordinates [Finite U] (hc : Nat.card U=81) :
    ∃ E : V ≃ₗ[ZMod 3] U,
      (∀ v, M.rotation (E v)=E (a v)) ∧
      (∀ v, M.reflection (E v)=E (r v)) ∧
      (∀ k v, quaternionWord M.rotation M.reflection k (E v)=E (q k v)) := by
  obtain ⟨F,hA,hR⟩ := M.quaternion.exists_coordinates hc
  let E := tupleCoordinates.trans F
  have hAE (v : V) : M.rotation (E v)=E (a v) := hA (tupleCoordinates v)
  have hRE (v : V) : M.reflection (E v)=E (r v) := hR (tupleCoordinates v)
  refine ⟨E,hAE,hRE,?_⟩
  intro k v
  fin_cases k <;> simp [quaternionWord,q,qi,qj,hAE,hRE,←map_neg]

/-- Simultaneous coordinates for the actual reflection, cubic and quaternion subgroup. -/
theorem exists_marked_coordinates [Finite U] (hc : Nat.card U=81) :
    ∃ E : U ≃ₗ[ZMod 3] V,
      (∀ v, E (M.reflection v)=r (E v)) ∧
      (∀ v, E (M.cubic v)=lin y0 (E v)) ∧
      (∀ k : Fin 8, ∃ j : Fin 8, ∀ v,
        E (quaternionWord M.rotation M.reflection k v)=q j (E v)) ∧
      (∀ j : Fin 8, ∃ k : Fin 8, ∀ v,
        E (quaternionWord M.rotation M.reflection k v)=q j (E v)) := by
  obtain ⟨F,hA,hR,hQ⟩ := M.exists_quaternion_coordinates hc
  let f := (F.toAddEquiv.trans (M.cubic.toAddEquiv.trans F.symm.toAddEquiv)).toAddMonoidHom
  have hf (v : V) : f v=F.symm (M.cubic (F v)) := rfl
  have hfc : ∀ v, f (f (f v))=v := by
    intro v
    simp only [hf,LinearEquiv.apply_symm_apply,M.cubic_cube,LinearEquiv.symm_apply_apply]
  have hfr : ∀ v, r (f v)=f (f (r v)) := by
    intro v
    apply F.injective
    simp only [hf,LinearEquiv.apply_symm_apply,←hR,M.inverts_cubic]
  have hfn : ∃ v, f v≠v := by
    obtain ⟨v,hv⟩ := M.cubic_nontrivial
    refine ⟨F.symm v,?_⟩
    intro he
    apply hv
    have hh := congrArg F he
    simpa only [hf,LinearEquiv.apply_symm_apply] using hh
  have hfQ : ∀ k : Fin 8, ∃ j : Fin 8, ∀ v, f (q k v)=q j (f v) := by
    intro k
    obtain ⟨j,hj⟩ := M.normalizes k
    refine ⟨j,?_⟩
    intro v
    apply F.injective
    simp only [hf,LinearEquiv.apply_symm_apply,←hQ,hj]
  obtain ⟨T,m,hm,hTc,hTr,hTQ,hTQ',hTB⟩ := exists_cubic_transport f hfc hfr hfn hfQ
  let E : U ≃ₗ[ZMod 3] V :=
    { F.symm.toAddEquiv.trans T with map_smul' := ZMod.map_smul (F.symm.toAddEquiv.trans T).toAddMonoidHom }
  have hE (v : U) : E v=T (F.symm v) := rfl
  have hEQ (k : Fin 8) (v : U) :
      F.symm (quaternionWord M.rotation M.reflection k v)=q k (F.symm v) := by
    apply F.injective
    rw [LinearEquiv.apply_symm_apply,←hQ,LinearEquiv.apply_symm_apply]
  refine ⟨E,?_,?_,?_,?_⟩
  · intro v
    rw [hE,hE]
    have hh : F.symm (M.reflection v)=r (F.symm v) := by
      apply F.injective
      rw [LinearEquiv.apply_symm_apply,←hR,LinearEquiv.apply_symm_apply]
    rw [hh,hTr]
  · intro v
    have hh := hTc (F.symm v)
    simpa only [hf,LinearEquiv.apply_symm_apply,hE] using hh
  · intro k
    obtain ⟨j,hj⟩ := hTQ k
    exact ⟨j,fun v => by rw [hE,hEQ,hj,hE]⟩
  · intro j
    obtain ⟨k,hk⟩ := hTQ' j
    exact ⟨k,fun v => by rw [hE,hEQ,hk,hE]⟩
/-- The marked action determines its nondegenerate alternating form up to a
nonzero scalar, hence determines its full similitude class. -/
theorem exists_marked_form_coordinates [Finite U] (hc : Nat.card U=81)
    (B : LinearMap.BilinForm (ZMod 3) U) (hAlt : B.IsAlt)
    (hN : ∀ x, (∀ y, B x y=0) → x=0)
    (hQ : ∀ (k : Fin 8) x y,
      B (quaternionWord M.rotation M.reflection k x)
        (quaternionWord M.rotation M.reflection k y)=B x y)
    (hR : ∀ x y, B (M.reflection x) (M.reflection y)= -B x y) :
    ∃ (E : U ≃ₗ[ZMod 3] V) (b : ZMod 3), b≠0 ∧
      (∀ v, E (M.reflection v)=r (E v)) ∧
      (∀ v, E (M.cubic v)=lin y0 (E v)) ∧
      (∀ k : Fin 8, ∃ j : Fin 8, ∀ v,
        E (quaternionWord M.rotation M.reflection k v)=q j (E v)) ∧
      (∀ j : Fin 8, ∃ k : Fin 8, ∀ v,
        E (quaternionWord M.rotation M.reflection k v)=q j (E v)) ∧
      (∀ x y, B x y=b*standardForm (E x) (E y)) := by
  obtain ⟨E,hEr,hEc,hEQ,hEQ'⟩ := M.exists_marked_coordinates hc
  let B' := B.comp E.symm.toLinearMap E.symm.toLinearMap
  have hB' (x y : V) : B' x y=B (E.symm x) (E.symm y) := rfl
  have hAlt' : B'.IsAlt := fun x=>hAlt (E.symm x)
  have hQ' (j : Fin 8) (x y : V) : B' (q j x) (q j y)=B' x y := by
    obtain ⟨k,hk⟩ := hEQ' j
    have hh (v : V) : E.symm (q j v)=quaternionWord M.rotation M.reflection k (E.symm v) := by
      apply E.injective
      rw [LinearEquiv.apply_symm_apply,hk,LinearEquiv.apply_symm_apply]
    simp only [hB',hh,hQ]
  have hR' (x y : V) : B' (r x) (r y)= -B' x y := by
    have hh (v : V) : E.symm (r v)=M.reflection (E.symm v) := by
      apply E.injective
      rw [LinearEquiv.apply_symm_apply,hEr,LinearEquiv.apply_symm_apply]
    simp only [hB',hh,hR]
  have hform := form_unique B' hAlt' (hQ' 2) (hQ' 4) hR'
  have hb : B' (e 0) (e 1)≠0 := by
    intro he
    have hz := hN (E.symm (e 0)) (fun y=>by
      have hh := hform (e 0) (E y)
      rw [he,zero_mul] at hh
      simpa only [hB',LinearEquiv.symm_apply_apply] using hh)
    have hh := congrArg E hz
    have hn : e 0≠0 := by decide +kernel
    exact hn (by simpa only [LinearEquiv.apply_symm_apply,map_zero] using hh)
  refine ⟨E,B' (e 0) (e 1),hb,hEr,hEc,hEQ,hEQ',?_⟩
  intro x y
  simpa only [hB',LinearEquiv.symm_apply_apply] using hform (E x) (E y)

end MarkedAction
end Theory.Representation.QuaternionSixteenTernary
