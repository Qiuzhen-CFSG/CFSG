module

public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupAction.TernaryThreeEightModel
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic
/-!
# Fixed-free order-eight actions on ternary three-space

Every fixed-free automorphism of order eight of an elementary abelian group
of order 27 is conjugate to the standard torus or its inverse.

A basis first identifies the group with the additive group of F₃³. For a
linear map A, the vectors (A⁴ + I)eᵢ lie on its negated line and the vectors
(A⁴ - I)eⱼ lie on its irreducible plane. A finite, kernel-checked certificate
chooses a nonzero vector u on the line and a vector v on the plane so that
(u,v,Av) is a basis and A²v = v ± Av. These two companion forms give the
standard torus and, after interchanging the plane basis vectors, its inverse.
The certificate is split according to the image of the first basis vector.

This is the elementary abelian alternative in the q = 3 specialization of
Suzuki's 1965 unitary recognition argument, Section III, Lemma 12. The theorem
itself uses only the stated elementary group and automorphism hypotheses.
-/

namespace TernaryThreeEight
private def tupleEquiv : (Fin 3 → ZMod 3) ≃+ (ZMod 3 × ZMod 3 × ZMod 3) where
  toFun v := (v 0,v 1,v 2)
  invFun v := ![v.1,v.2.1,v.2.2]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv v := rfl
  map_add' v w := rfl

private theorem exists_ternary_equiv
    {P : Type*} [CommGroup P] [Finite P]
    (hcard : Nat.card P = 27) (hcube : ∀ x : P, x^3 = 1) : Nonempty (P ≃* V) := by
  let : IsElementaryAbelian 3 P :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hcube }
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive P) = 3 ^ 3 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive P)
    change Nat.card P = _ at hsize
    simpa only [Nat.card_zmod, hcard, show (3 : ℕ) ^ 3 = 27 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 3) (Additive P) = 3 :=
    Nat.pow_right_injective (by decide : 1 < 3) hpow
  let basis := Module.finBasisOfFinrankEq (ZMod 3) (Additive P) hdim
  exact ⟨AddEquiv.toMultiplicativeRight (basis.equivFun.toAddEquiv.trans tupleEquiv)⟩

namespace NormalFormInternal
abbrev W := ZMod 3 × ZMod 3 × ZMod 3
def lin (a b c : W) (v : W) : W :=
  (v.1*a.1+v.2.1*b.1+v.2.2*c.1,
   v.1*a.2.1+v.2.1*b.2.1+v.2.2*c.2.1,
   v.1*a.2.2+v.2.1*b.2.2+v.2.2*c.2.2)
def e : Fin 3 → W := ![(1,0,0),(0,1,0),(0,0,1)]
def good (a b c : W) : Prop :=
  (∀ i : Fin 3, (lin a b c)^[8] (e i) = e i) ∧
  (∃ i : Fin 3, (lin a b c)^[4] (e i) ≠ e i) ∧
  (∀ v : W, lin a b c v = v → v = 0)
instance (a b c : W) : Decidable (good a b c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def frame (a b c : W) (i j : Fin 3) : W × W × W :=
  let u := (lin a b c)^[4] (e i) + e i
  let v := (lin a b c)^[4] (e j) - e j
  (u,v,lin a b c v)
def valid (a b c : W) (i j : Fin 3) : Prop :=
  let (u,v,w) := frame a b c i j
  (∀ x : W, lin u v w x = 0 → x = 0) ∧
  lin a b c u = -u ∧
  (lin a b c w = v+w ∨ lin a b c w = v-w)
instance (a b c : W) (i j : Fin 3) : Decidable (valid a b c i j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def linHom (a b c : W) : W →+ W where
  toFun := lin a b c
  map_zero' := by ext <;> simp [lin]
  map_add' x y := by ext <;> simp [lin] <;> ring

theorem lin_nsmul (a b c x : W) :
    lin a b c x = x.1.val • a + x.2.1.val • b + x.2.2.val • c := by
  ext <;> simp [lin, nsmul_eq_mul]

theorem expansion (x : W) :
    x = x.1.val • e 0 + x.2.1.val • e 1 + x.2.2.val • e 2 := by
  ext <;> simp [e, nsmul_eq_mul]

theorem map_lin (f : W →+ W) (a b c x : W) :
    f (lin a b c x) = lin (f a) (f b) (f c) x := by
  simp only [lin_nsmul, map_add, map_nsmul]

theorem representation (f : W →+ W) (x : W) :
    f x = lin (f (e 0)) (f (e 1)) (f (e 2)) x := by
  conv_lhs => rw [expansion x]
  simp only [map_add, map_nsmul, lin_nsmul]

theorem ext_basis (f g : W →+ W) (h : ∀ i, f (e i) = g (e i)) : f = g := by
  apply AddMonoidHom.ext
  intro x
  rw [representation f x, representation g x, h 0, h 1, h 2]

def additive (f : MulAut TernaryThreeEight.V) : W ≃+ W where
  toFun v := (f (Multiplicative.ofAdd v)).toAdd
  invFun v := (f.symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := f.left_inv v
  right_inv v := f.right_inv v
  map_add' v w := f.map_mul v w

theorem iterate_additive (f : MulAut TernaryThreeEight.V) (n : ℕ) (x : W) :
    (additive f)^[n] x = ((f^n) (Multiplicative.ofAdd x)).toAdd := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', pow_succ', MulAut.mul_apply]
    exact congrArg (additive f) ih

theorem good_of_aut (f : MulAut TernaryThreeEight.V) (hf : orderOf f = 8)
    (hfixed : ∀ x, f x = x → x = 1) :
    good (additive f (e 0)) (additive f (e 1)) (additive f (e 2)) := by
  have hrep : lin (additive f (e 0)) (additive f (e 1)) (additive f (e 2)) =
      additive f := funext fun x => (representation (additive f).toAddMonoidHom x).symm
  have h8 : f^8 = 1 := hf ▸ pow_orderOf_eq_one f
  unfold good
  rw [hrep]
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [iterate_additive, h8]
    rfl
  · by_contra h
    push Not at h
    have hf4 : f^4 = 1 := by
      have heq : (additive (f^4)).toAddMonoidHom = AddMonoidHom.id W :=
        ext_basis _ _ (by intro i; exact (iterate_additive f 4 (e i)).symm.trans (h i))
      apply MulEquiv.ext
      intro x
      exact congrArg (fun g : W →+ W => g x.toAdd) heq
    have hd := orderOf_dvd_of_pow_eq_one hf4
    rw [hf] at hd
    norm_num at hd
  · intro x hx
    exact hfixed (Multiplicative.ofAdd x) hx

-- The two companion forms on the plane.
theorem lin_torus (u v w : W) (x : TernaryThreeEight.V) :
    lin u v w (TernaryThreeEight.torus x).toAdd =
      lin (-u) w (v+w) x.toAdd := by
  ext <;> simp [lin, TernaryThreeEight.torus] <;> ring

theorem lin_torus_inv (u v w : W) (x : TernaryThreeEight.V) :
    lin u w v ((TernaryThreeEight.torus⁻¹) x).toAdd =
      lin (-u) (v-w) w x.toAdd := by
  ext <;> simp [lin, TernaryThreeEight.torus, MulAut.inv_apply] <;> ring
noncomputable def linAut (u v w : W)
    (h : ∀ x, lin u v w x = 0 → x = 0) : MulAut TernaryThreeEight.V :=
  let hinj := (injective_iff_map_eq_zero (linHom u v w)).mpr h
  AddEquiv.toMultiplicative (AddEquiv.ofBijective (linHom u v w)
    ⟨hinj,Finite.surjective_of_injective hinj⟩)

theorem swap_kernel (u v w : W) (h : ∀ x, lin u v w x = 0 → x = 0) :
    ∀ x, lin u w v x = 0 → x = 0 := by
  intro x hx
  have hs : lin u v w (x.1,x.2.2,x.2.1) = lin u w v x := by
    ext <;> simp [lin] <;> ring
  have hz := h _ (hs.trans hx)
  have hz1 := congrArg (fun t : W => t.1) hz
  have hz2 := congrArg (fun t : W => t.2.1) hz
  have hz3 := congrArg (fun t : W => t.2.2) hz
  exact Prod.ext hz1 (Prod.ext hz3 hz2)

theorem frame_conjugacy (f : MulAut TernaryThreeEight.V)
    (i j : Fin 3)
    (hvalid : valid (additive f (e 0)) (additive f (e 1)) (additive f (e 2)) i j) :
    ∃ g : MulAut TernaryThreeEight.V,
      (∀ x, f (g x) = g (TernaryThreeEight.torus x)) ∨
      (∀ x, f (g x) = g ((TernaryThreeEight.torus⁻¹) x)) := by
  let a := additive f (e 0)
  let b := additive f (e 1)
  let c := additive f (e 2)
  let u := (frame a b c i j).1
  let v := (frame a b c i j).2.1
  let w := (frame a b c i j).2.2
  obtain ⟨hk, hu, hw⟩ := hvalid
  have hfu : additive f u = -u := (representation (additive f).toAddMonoidHom u).trans hu
  have hfv : additive f v = w := representation (additive f).toAddMonoidHom v
  rcases hw with hw | hw
  · have hfw : additive f w = v+w := (representation (additive f).toAddMonoidHom w).trans hw
    refine ⟨linAut u v w hk, Or.inl ?_⟩
    intro x
    change (additive f).toAddMonoidHom (lin u v w x.toAdd) = lin u v w (TernaryThreeEight.torus x).toAdd
    rw [map_lin (additive f).toAddMonoidHom]
    change lin (additive f u) (additive f v) (additive f w) x.toAdd = _
    rw [hfu, hfv, hfw]
    exact (lin_torus u v w x).symm
  · have hfw : additive f w = v-w := (representation (additive f).toAddMonoidHom w).trans hw
    refine ⟨linAut u w v (swap_kernel u v w hk), Or.inr ?_⟩
    intro x
    change (additive f).toAddMonoidHom (lin u w v x.toAdd) = lin u w v ((TernaryThreeEight.torus⁻¹) x).toAdd
    rw [map_lin (additive f).toAddMonoidHom]
    change lin (additive f u) (additive f w) (additive f v) x.toAdd = _
    rw [hfu, hfv, hfw]
    exact (lin_torus_inv u v w x).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_000 : ∀ b c : W,
    good (0,0,0) b c → ∃ i j : Fin 3, valid (0,0,0) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_001 : ∀ b c : W,
    good (0,0,1) b c → ∃ i j : Fin 3, valid (0,0,1) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_002 : ∀ b c : W,
    good (0,0,2) b c → ∃ i j : Fin 3, valid (0,0,2) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_010 : ∀ b c : W,
    good (0,1,0) b c → ∃ i j : Fin 3, valid (0,1,0) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_011 : ∀ b c : W,
    good (0,1,1) b c → ∃ i j : Fin 3, valid (0,1,1) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_012 : ∀ b c : W,
    good (0,1,2) b c → ∃ i j : Fin 3, valid (0,1,2) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_020 : ∀ b c : W,
    good (0,2,0) b c → ∃ i j : Fin 3, valid (0,2,0) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_021 : ∀ b c : W,
    good (0,2,1) b c → ∃ i j : Fin 3, valid (0,2,1) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_022 : ∀ b c : W,
    good (0,2,2) b c → ∃ i j : Fin 3, valid (0,2,2) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_100 : ∀ b c : W,
    good (1,0,0) b c → ∃ i j : Fin 3, valid (1,0,0) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_101 : ∀ b c : W,
    good (1,0,1) b c → ∃ i j : Fin 3, valid (1,0,1) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_102 : ∀ b c : W,
    good (1,0,2) b c → ∃ i j : Fin 3, valid (1,0,2) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_110 : ∀ b c : W,
    good (1,1,0) b c → ∃ i j : Fin 3, valid (1,1,0) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_111 : ∀ b c : W,
    good (1,1,1) b c → ∃ i j : Fin 3, valid (1,1,1) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_112 : ∀ b c : W,
    good (1,1,2) b c → ∃ i j : Fin 3, valid (1,1,2) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_120 : ∀ b c : W,
    good (1,2,0) b c → ∃ i j : Fin 3, valid (1,2,0) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_121 : ∀ b c : W,
    good (1,2,1) b c → ∃ i j : Fin 3, valid (1,2,1) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_122 : ∀ b c : W,
    good (1,2,2) b c → ∃ i j : Fin 3, valid (1,2,2) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_200 : ∀ b c : W,
    good (2,0,0) b c → ∃ i j : Fin 3, valid (2,0,0) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_201 : ∀ b c : W,
    good (2,0,1) b c → ∃ i j : Fin 3, valid (2,0,1) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_202 : ∀ b c : W,
    good (2,0,2) b c → ∃ i j : Fin 3, valid (2,0,2) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_210 : ∀ b c : W,
    good (2,1,0) b c → ∃ i j : Fin 3, valid (2,1,0) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_211 : ∀ b c : W,
    good (2,1,1) b c → ∃ i j : Fin 3, valid (2,1,1) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_212 : ∀ b c : W,
    good (2,1,2) b c → ∃ i j : Fin 3, valid (2,1,2) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_220 : ∀ b c : W,
    good (2,2,0) b c → ∃ i j : Fin 3, valid (2,2,0) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_221 : ∀ b c : W,
    good (2,2,1) b c → ∃ i j : Fin 3, valid (2,2,1) b c i j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem certificate_222 : ∀ b c : W,
    good (2,2,2) b c → ∃ i j : Fin 3, valid (2,2,2) b c i j := by
  decide +kernel

private theorem certificate : ∀ a b c : W,
    good a b c → ∃ i j : Fin 3, valid a b c i j := by
  rintro ⟨a₀,a₁,a₂⟩
  fin_cases a₀ <;> fin_cases a₁ <;> fin_cases a₂
  · exact certificate_000
  · exact certificate_001
  · exact certificate_002
  · exact certificate_010
  · exact certificate_011
  · exact certificate_012
  · exact certificate_020
  · exact certificate_021
  · exact certificate_022
  · exact certificate_100
  · exact certificate_101
  · exact certificate_102
  · exact certificate_110
  · exact certificate_111
  · exact certificate_112
  · exact certificate_120
  · exact certificate_121
  · exact certificate_122
  · exact certificate_200
  · exact certificate_201
  · exact certificate_202
  · exact certificate_210
  · exact certificate_211
  · exact certificate_212
  · exact certificate_220
  · exact certificate_221
  · exact certificate_222

theorem concrete_normal_form
    (f : MulAut TernaryThreeEight.V) (hf : orderOf f = 8)
    (hfixed : ∀ x, f x = x → x = 1) :
    ∃ a : MulAut TernaryThreeEight.V,
      (∀ x, a (f x) = TernaryThreeEight.torus (a x)) ∨
      (∀ x, a ((f⁻¹) x) = TernaryThreeEight.torus (a x)) := by
  obtain ⟨i,j,hij⟩ := certificate _ _ _ (good_of_aut f hf hfixed)
  obtain ⟨g,hg | hg⟩ := frame_conjugacy f i j hij
  · refine ⟨g.symm, Or.inl ?_⟩
    intro x
    apply g.injective
    simpa only [MulEquiv.apply_symm_apply] using (hg (g.symm x))
  · refine ⟨g.symm, Or.inr ?_⟩
    intro x
    apply g.injective
    simp only [MulEquiv.apply_symm_apply]
    apply f.injective
    rw [hg]
    simp only [MulAut.inv_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
end NormalFormInternal

/-- A fixed-free order-eight action on an elementary abelian group of order 27
has the standard ternary form, up to inversion of the acting automorphism. -/
public theorem exists_normal_form
    {P : Type*} [CommGroup P] [Finite P]
    (hcard : Nat.card P = 27) (hcube : ∀ x : P, x^3 = 1)
    (f : MulAut P) (hf : orderOf f = 8)
    (hfixed : ∀ x, f x = x → x = 1) :
    ∃ e : P ≃* V, (∀ x, e (f x) = torus (e x)) ∨
      (∀ x, e ((f⁻¹) x) = torus (e x)) := by
  obtain ⟨e⟩ := exists_ternary_equiv hcard hcube
  let t := (MulAut.congr e) f
  have ht : orderOf t = 8 := ((MulAut.congr e).orderOf_eq f).trans hf
  have htfixed : ∀ v, t v = v → v = 1 := by
    intro v hv
    change e (f (e.symm v)) = v at hv
    have h := congrArg e.symm hv
    simp only [MulEquiv.symm_apply_apply] at h
    have h' := congrArg e (hfixed (e.symm v) h)
    simpa only [MulEquiv.apply_symm_apply, map_one] using h'
  obtain ⟨a,ha | ha⟩ := NormalFormInternal.concrete_normal_form t ht htfixed
  · refine ⟨e.trans a, Or.inl ?_⟩
    intro x
    have h := ha (e x)
    change a (e (f (e.symm (e x)))) = torus (a (e x)) at h
    simpa only [MulEquiv.symm_apply_apply, MulEquiv.trans_apply] using h
  · refine ⟨e.trans a, Or.inr ?_⟩
    intro x
    have h := ha (e x)
    have htinv : t⁻¹ = (MulAut.congr e) (f⁻¹) := (map_inv (MulAut.congr e) f).symm
    rw [htinv] at h
    change a (e ((f⁻¹) (e.symm (e x)))) = torus (a (e x)) at h
    simpa only [MulEquiv.symm_apply_apply, MulEquiv.trans_apply] using h
end TernaryThreeEight
