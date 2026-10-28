module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.HermitianAction
public import Theory.GroupTheory.PCoreFrattiniAction

/-!
# Involutions centralizing the unitary-five plane-core center

The square of a plane parameter has matrix coordinate x x*. An automorphism
fixing the center therefore preserves this rank-one Hermitian matrix on the
vector quotient. Additivity forces its vector action to be multiplication
by a norm-one scalar. If the automorphism squares to one, characteristic two
forces that scalar to be one. The literal Frattini action then places every
involution centralizing the center in the two-core of a characteristic-two
overgroup with this core.

This is the outer-actor step needed to extend the inner Thompson calculation
to the original ambient Sylow in the Chapter6 companion. No identification of
the whole ambient group is used.
Source: Aschbacher–Smith F.4.29(6), F.4.35, printed pp.289,292.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore.Parameters
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

omit [CharP F 2] in
private theorem norm_zero {a : F} (h : a * J.conj a = 0) : a = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact J.conj.injective (h.trans (map_zero _).symm)

omit [CharP F 2] in
private theorem vector_scalar (f : (Fin 2 → F) →+ (Fin 2 → F))
    (hf : ∀ x i j, f x i * J.conj (f x j) = x i * J.conj (x j)) :
    ∃ a : F, a * J.conj a = 1 ∧ ∀ x i, f x i = a * x i := by
  let a := f ![1,0] 0
  let b := f ![0,1] 1
  have hzero0 (t : F) : f ![0,t] 0 = 0 := norm_zero J (by simpa using hf ![0,t] 0 0)
  have hzero1 (t : F) : f ![t,0] 1 = 0 := norm_zero J (by simpa using hf ![t,0] 1 1)
  have hparts (s t : F) : f ![s,t] = ![f ![s,0] 0,f ![0,t] 1] := by
    have he : (![s,t] : Fin 2 → F) = ![s,0] + ![0,t] := by ext i; fin_cases i <;> simp
    rw [he,map_add]
    ext i
    fin_cases i <;> simp [hzero0,hzero1]
  have haa : a * J.conj a = 1 := by simpa [a] using hf ![1,0] 0 0
  have hab : a * J.conj b = 1 := by
    have hh := hf ![1,1] 0 1
    rw [hparts] at hh
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      map_one,mul_one] using hh
  have ha : a ≠ 0 := by intro ha; simp [ha] at haa
  have hb : b = a := J.conj.injective (mul_left_cancel₀ ha (hab.trans haa.symm))
  have hca : J.conj a ≠ 0 := by intro hz; simp [hz] at haa
  have hfirst (s : F) : f ![s,0] 0 = a * s := by
    apply mul_right_cancel₀ hca
    have hh := hf ![s,1] 0 1
    rw [hparts] at hh
    change f ![s,0] 0 * J.conj b = s * J.conj 1 at hh
    rw [hb,map_one,mul_one] at hh
    calc
      _ = s := hh
      _ = a * s * J.conj a := by rw [mul_right_comm,haa,one_mul]
  have hsecond (t : F) : f ![0,t] 1 = a * t := by
    apply J.conj.injective
    apply mul_left_cancel₀ ha
    have hh := hf ![1,t] 0 1
    rw [hparts] at hh
    change a * J.conj (f ![0,t] 1) = 1 * J.conj t at hh
    rw [map_mul,←mul_assoc,haa,one_mul]
    simpa using hh
  refine ⟨a,haa,?_⟩
  intro x i
  have he : x = ![x 0,x 1] := by ext j; fin_cases j <;> rfl
  rw [he,hparts]
  fin_cases i
  · exact hfirst (x 0)
  · exact hsecond (x 1)

private theorem vector_eq_of_involutive (f : (Fin 2 → F) →+ (Fin 2 → F))
    (hf : ∀ x i j, f x i * J.conj (f x j) = x i * J.conj (x j))
    (hff : Function.Involutive f) (x : Fin 2 → F) : f x = x := by
  obtain ⟨a,_,ha⟩ := vector_scalar J f hf
  have hsq := congrFun (hff ![1,0]) 0
  rw [ha,ha] at hsq
  have ha1 : a = 1 := by
    have haa : a * a = 1 := by simpa using hsq
    rcases mul_self_eq_one_iff.mp haa with hh | hh
    · exact hh
    · simpa only [CharTwo.neg_eq] using hh
  ext i
  rw [ha,ha1,one_mul]

def vectorAction (c : F) (hc : c + J.conj c = 1) (a : MulAut (Parameters J)) :
    Multiplicative (Fin 2 → F) →* Multiplicative (Fin 2 → F) :=
  (vectorHom J).liftOfSurjective (vectorHom_surjective J c hc)
    ⟨(vectorHom J).comp a.toMonoidHom, by
      intro u hu
      change a u ∈ (vectorHom J).ker
      rw [←center_eq_vector_ker J c hc] at hu ⊢
      exact MulEquivClass.apply_mem_center a hu⟩

theorem vectorAction_apply (c : F) (hc : c + J.conj c = 1)
    (a : MulAut (Parameters J)) (u : Parameters J) :
    vectorAction J c hc a (vectorHom J u) = vectorHom J (a u) := by
  unfold vectorAction
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- An involutory automorphism fixing the whole center fixes every vector
coordinate, hence the literal Frattini quotient. -/
theorem vector_fixed_of_center_fixed (c : F) (hc : c + J.conj c = 1)
    (a : MulAut (Parameters J)) (ha : a ^ 2 = 1)
    (hz : ∀ u ∈ center (Parameters J), a u = u) (u : Parameters J) :
    (a u).x = u.x := by
  let f : (Fin 2 → F) →+ (Fin 2 → F) := (vectorAction J c hc a).toAdditive
  have he (v : Parameters J) : f v.x = (a v).x :=
    congrArg Multiplicative.toAdd (vectorAction_apply J c hc a v)
  have hn (x : Fin 2 → F) (i j : Fin 2) : f x i * J.conj (f x j) = x i * J.conj (x j) := by
    obtain ⟨v,hv⟩ := vectorHom_surjective J c hc (Multiplicative.ofAdd x)
    have hv' : v.x = x := congrArg Multiplicative.toAdd hv
    rw [←hv',he]
    have hs := hz (v ^ 2) (mem_center_of_x_eq_zero J _ (by
      ext k; simp [pow_two,CharTwo.add_self_eq_zero]))
    rw [map_pow] at hs
    have hh := congrArg (fun v : Parameters J => v.z i j) hs
    simpa [pow_two,CharTwo.add_self_eq_zero] using hh
  have hff : Function.Involutive f := by
    intro x
    obtain ⟨v,hv⟩ := vectorHom_surjective J c hc (Multiplicative.ofAdd x)
    have hv' : v.x = x := congrArg Multiplicative.toAdd hv
    rw [←hv',he,he]
    have hh : a (a v) = v := by
      have hh := congrArg (fun b : MulAut (Parameters J) => b v) ha
      simpa [pow_two] using hh
    rw [hh]
  exact (he u).symm.trans (vector_eq_of_involutive J f hn hff u.x)

/-- A two-power-order automorphism fixing the center fixes the vector quotient.
The scalar detected by the square map has no nontrivial two-power torsion. -/
theorem vector_fixed_of_center_fixed_two_power (c : F) (hc : c + J.conj c = 1)
    (a : MulAut (Parameters J)) (k : ℕ) (ha : a ^ (2^k) = 1)
    (hz : ∀ u ∈ center (Parameters J), a u = u) (u : Parameters J) :
    (a u).x = u.x := by
  let f : (Fin 2 → F) →+ (Fin 2 → F) := (vectorAction J c hc a).toAdditive
  have he (v : Parameters J) : f v.x = (a v).x :=
    congrArg Multiplicative.toAdd (vectorAction_apply J c hc a v)
  have hn (x : Fin 2 → F) (i j : Fin 2) : f x i * J.conj (f x j) = x i * J.conj (x j) := by
    obtain ⟨v,hv⟩ := vectorHom_surjective J c hc (Multiplicative.ofAdd x)
    have hv' : v.x = x := congrArg Multiplicative.toAdd hv
    rw [←hv',he]
    have hs := hz (v ^ 2) (mem_center_of_x_eq_zero J _ (by
      ext j; simp [pow_two,CharTwo.add_self_eq_zero]))
    rw [map_pow] at hs
    have hh := congrArg (fun v : Parameters J => v.z i j) hs
    simpa [pow_two,CharTwo.add_self_eq_zero] using hh
  obtain ⟨s,_,hs⟩ := vector_scalar J f hn
  have hp (m : ℕ) (v : Parameters J) (i : Fin 2) : ((a^m) v).x i = s^m * v.x i := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ',MulAut.mul_apply,←he,hs,ih,pow_succ',mul_assoc]
  obtain ⟨v,hv⟩ := vectorHom_surjective J c hc (Multiplicative.ofAdd ![1,0])
  have hv0 : v.x 0 = 1 := congrArg (fun x => x.toAdd 0) hv
  have hs1 : s = 1 := by
    apply (iterateFrobenius F 2 k).injective
    change s^(2^k) = 1^(2^k)
    have hh := hp (2^k) v 0
    rw [ha,MulAut.one_apply,hv0,mul_one] at hh
    simpa only [one_pow] using hh.symm
  ext i
  rw [←he,hs,hs1,one_mul]

end Theory.SpecificGroups.UnitaryFive.PlaneCore.Parameters

namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
open Subgroup
variable {F R : Type*} [Field F] [CharP F 2] [Finite F] [Group R] [Finite R]
  (J : HermitianForm 5 F)

/-- In a characteristic-two overgroup with this actual core, every
two-element centralizing the core center belongs to the core. -/
theorem twoElement_mem_core_of_center_centralizing
    (e : pCore 2 R ≃* Parameters J) (c : F) (hc : c + J.conj c = 1)
    (hself : centralizer (pCore 2 R : Set R) ≤ pCore 2 R)
    (r : R) (k : ℕ) (hr : r ^ (2^k) = 1)
    (hz : r ∈ centralizer ((center (pCore 2 R)).map (pCore 2 R).subtype : Set R)) :
    r ∈ pCore 2 R := by
  let a := (MulAut.congr e) (MulAut.conjNormal r)
  have ha : a ^ (2^k) = 1 := by
    change ((MulAut.congr e) (MulAut.conjNormal r)) ^ (2^k) = 1
    rw [←map_pow,←map_pow,hr,map_one,map_one]
  have haz : ∀ u ∈ center (Parameters J), a u = u := by
    intro u hu
    have hv : e.symm u ∈ center (pCore 2 R) := MulEquivClass.apply_mem_center e.symm hu
    have hh : MulAut.conjNormal r (e.symm u) = e.symm u := by
      apply Subtype.ext
      change r * (e.symm u).val * r⁻¹ = (e.symm u).val
      rw [←hz (e.symm u).val ⟨e.symm u,hv,rfl⟩,mul_inv_cancel_right]
    change e (MulAut.conjNormal r (e.symm u)) = u
    rw [hh,e.apply_symm_apply]
  have hact : quotientAut (frattini (pCore 2 R)) (MulAut.conjNormal r) = 1 := by
    apply MulEquiv.ext
    intro v
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (frattini (pCore 2 R)) v
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini (pCore 2 R)) (MulAut.conjNormal r u) =
      QuotientGroup.mk' (frattini (pCore 2 R)) u
    apply (QuotientGroup.mk'_eq_mk' (frattini (pCore 2 R))).mpr
    refine ⟨(MulAut.conjNormal r u)⁻¹ * u,?_,by simp⟩
    have hh := Parameters.vector_fixed_of_center_fixed_two_power J c hc a k ha haz (e u)
    change (e (MulAut.conjNormal r (e.symm (e u)))).x = (e u).x at hh
    rw [e.symm_apply_apply] at hh
    have he : e ((MulAut.conjNormal r u)⁻¹ * u) ∈ center (Parameters J) := by
      apply Parameters.mem_center_of_x_eq_zero
      rw [map_mul,map_inv,Parameters.mul_x,Parameters.inv_x,hh]
      ext i
      exact CharTwo.add_self_eq_zero _
    rw [←Parameters.frattini_eq_center J c hc,←frattini_map_equiv e] at he
    exact (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp he
  have hk : r ∈ ((quotientAut (frattini (pCore 2 R))).comp
      (MulAut.conjNormal : R →* MulAut (pCore 2 R))).ker := hact
  rwa [pCore_frattini_action_kernel 2 hself] at hk

/-- The square-one specialization retains the original involution interface. -/
theorem involution_mem_core_of_center_centralizing
    (e : pCore 2 R ≃* Parameters J) (c : F) (hc : c + J.conj c = 1)
    (hself : centralizer (pCore 2 R : Set R) ≤ pCore 2 R)
    (r : R) (hr : r ^ 2 = 1)
    (hz : r ∈ centralizer ((center (pCore 2 R)).map (pCore 2 R).subtype : Set R)) :
    r ∈ pCore 2 R :=
  twoElement_mem_core_of_center_centralizing J e c hc hself r 1 (by simpa using hr) hz

end Theory.SpecificGroups.UnitaryFive.PlaneCore
