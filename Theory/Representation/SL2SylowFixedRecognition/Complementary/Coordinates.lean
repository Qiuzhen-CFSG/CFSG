module
public import Theory.Representation.SL2SylowFixedRecognition.Complementary.Generators

/-!
# The field action reconstructed from complementary root spaces

The upper-root shear coefficients are additive. The diagonal word gives
C(a)C(b)C(a)=C(a²b); its square case forces the coefficients to commute.
Surjectivity of squaring in the finite binary field then gives multiplication.
A basis over this reconstructed field gives natural coordinates for every
original matrix actor, including the zero module. No irreducible constituent
classification or splitting hypothesis is used.

Source: Aschbacher--Smith, G.1.7, pp.329--330; a direct root-coordinate proof.
-/

@[expose] public noncomputable section
open Representation Matrix
open scoped MatrixGroups
namespace Representation.SL2SylowFixedRecognition.RootCoordinates
universe u
variable {F : Type*} [Field F]
variable {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
variable (σ : Representation (ZMod 2) SL(2,F) M) (w : SL(2,F))

structure RootPair (A : Submodule (ZMod 2) M) : Prop where
  complement : IsCompl A (A.map (σ w))
  fixed : ∀ t x, x ∈ A → σ (upper t) x = x
  moved : ∀ t x, σ (upper t) x - x ∈ A

variable {σ w} {A : Submodule (ZMod 2) M}

noncomputable def pairCoordinates (h : RootPair σ w A) : M ≃ₗ[ZMod 2] A × A :=
  (A.prodEquivOfIsCompl (A.map (σ w)) h.complement).symm.trans
    ((LinearEquiv.refl (ZMod 2) A).prodCongr
      (A.equivMapOfInjective (σ w) (fun x y he => by simpa only [σ.inv_self_apply] using congrArg (σ w⁻¹) he)).symm)

theorem pairCoordinates_symm_apply (h : RootPair σ w A) (x y : A) :
    (pairCoordinates h).symm (x,y) = (x : M) + σ w y := rfl

theorem pairCoordinates_self (h : RootPair σ w A) (x : A) :
    pairCoordinates h x = (x,0) := by
  apply (pairCoordinates h).symm.injective
  simp only [LinearEquiv.symm_apply_apply, pairCoordinates_symm_apply,
    ZeroMemClass.coe_zero, map_zero, add_zero]

theorem pairCoordinates_weyl (h : RootPair σ w A) (hw : w*w=1) (x : M) :
    pairCoordinates h (σ w x) = ((pairCoordinates h x).2,(pairCoordinates h x).1) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (pairCoordinates h).symm.surjective x
  simp only [LinearEquiv.apply_symm_apply]
  apply (pairCoordinates h).symm.injective
  simp only [LinearEquiv.symm_apply_apply,
    pairCoordinates_symm_apply, map_add]
  have hs (y : M) : σ w (σ w y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, hw, map_one, Module.End.one_apply]
  rw [hs, add_comm]

def coefficient (h : RootPair σ w A) (t : F) : Module.End (ZMod 2) A :=
  (((σ (upper t) - 1).comp (σ w)).comp A.subtype).codRestrict A
    (fun x => h.moved t (σ w x))

theorem coefficient_val (h : RootPair σ w A) (t : F) (x : A) :
    (coefficient h t x : M) = σ (upper t) (σ w x) - σ w x := rfl

theorem pairCoordinates_upper (h : RootPair σ w A) (t : F) (x : M) :
    pairCoordinates h (σ (upper t) x) =
      ((pairCoordinates h x).1 + coefficient h t (pairCoordinates h x).2,
       (pairCoordinates h x).2) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (pairCoordinates h).symm.surjective x
  simp only [LinearEquiv.apply_symm_apply]
  apply (pairCoordinates h).symm.injective
  simp only [LinearEquiv.symm_apply_apply,
    pairCoordinates_symm_apply, map_add, Submodule.coe_add, coefficient_val, h.fixed t a a.property]
  abel

theorem coefficient_one (h : RootPair σ w A) (hw : w*w=1)
    (hbraid : upper 1 * w * upper 1 = w * upper 1 * w) : coefficient h 1 = 1 := by
  apply LinearMap.ext
  intro x
  have he := congrArg (fun g => pairCoordinates h (σ g (x : M))) hbraid
  simp only [map_mul, Module.End.mul_apply, pairCoordinates_upper,
    pairCoordinates_weyl h hw, pairCoordinates_self, map_zero, add_zero, zero_add] at he
  exact congrArg Prod.fst he

theorem coefficient_add (h : RootPair σ w A) (t s : F)
    (hadd : upper (t+s) = upper t * upper s) :
    coefficient h (t+s) = coefficient h t + coefficient h s := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.add_apply, Submodule.coe_add, coefficient_val]
  rw [hadd, map_mul, Module.End.mul_apply]
  have hf := h.fixed t _ (h.moved s (σ w x))
  simp only [map_sub] at hf
  rw [sub_eq_iff_eq_add] at hf
  rw [hf]
  abel


theorem coefficient_zero (h : RootPair σ w A) : coefficient h 0 = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [coefficient_val,upper_zero]

variable [CharP F 2]

theorem coefficient_inv_mul (h : RootPair σ (weyl : SL(2,F)) A)
    (hd : ∀ a : F, a ≠ 0 → ∀ x ∈ A, σ (diagonalWord a) x ∈ A)
    {a : F} (ha : a ≠ 0) : coefficient h a⁻¹ * coefficient h a = 1 := by
  apply LinearMap.ext
  intro x
  have he := congrArg Prod.snd (pairCoordinates_self h ⟨_,hd a ha x x.property⟩)
  change (pairCoordinates h (σ (diagonalWord a) (x : M))).2 = 0 at he
  simp only [diagonalWord,map_mul,Module.End.mul_apply,pairCoordinates_upper,
    pairCoordinates_weyl h weyl_mul_self,pairCoordinates_self,zero_add] at he
  have hz (y : A) : y + y = 0 := by
    simpa only [one_smul,show (1 : ZMod 2)+1=0 from rfl,zero_smul] using
      (add_smul (1 : ZMod 2) 1 y).symm
  change coefficient h a⁻¹ (coefficient h a x) = x
  exact (eq_neg_of_add_eq_zero_right he).trans (neg_eq_of_add_eq_zero_left (hz x))

theorem coefficient_mul_inv (h : RootPair σ (weyl : SL(2,F)) A)
    (hd : ∀ a : F, a ≠ 0 → ∀ x ∈ A, σ (diagonalWord a) x ∈ A)
    {a : F} (ha : a ≠ 0) : coefficient h a * coefficient h a⁻¹ = 1 := by
  simpa only [inv_inv] using coefficient_inv_mul h hd (inv_ne_zero ha)

theorem pairCoordinates_diagonal (h : RootPair σ (weyl : SL(2,F)) A)
    (hd : ∀ a : F, a ≠ 0 → ∀ x ∈ A, σ (diagonalWord a) x ∈ A)
    {a : F} (ha : a ≠ 0) (x : M) :
    pairCoordinates h (σ (diagonalWord a) x) =
      (coefficient h a (pairCoordinates h x).1,
       coefficient h a⁻¹ (pairCoordinates h x).2) := by
  have hi (y : A) : coefficient h a⁻¹ (coefficient h a y) = y :=
    LinearMap.congr_fun (coefficient_inv_mul h hd ha) y
  have hj (y : A) : coefficient h a (coefficient h a⁻¹ y) = y :=
    LinearMap.congr_fun (coefficient_mul_inv h hd ha) y
  have hz (y : A) : y + y = 0 := by
    simpa only [one_smul,show (1 : ZMod 2)+1=0 from rfl,zero_smul] using
      (add_smul (1 : ZMod 2) 1 y).symm
  simp only [diagonalWord,map_mul,Module.End.mul_apply,pairCoordinates_upper,
    pairCoordinates_weyl h weyl_mul_self,map_add,hi,hj]
  apply Prod.ext <;> dsimp only
  · abel_nf
    simp only [show (3 : ℤ) = 2+1 from rfl,add_zsmul,two_zsmul,one_zsmul,hz,zero_add]
  · abel_nf
    simp only [two_zsmul,hz,zero_add]

theorem coefficient_sandwich (h : RootPair σ (weyl : SL(2,F)) A)
    (hd : ∀ a : F, a ≠ 0 → ∀ x ∈ A, σ (diagonalWord a) x ∈ A)
    (a b : F) : coefficient h a * coefficient h b * coefficient h a =
      coefficient h (a*a*b) := by
  by_cases ha : a = 0
  · simp [ha,coefficient_zero]
  apply LinearMap.ext
  intro x
  have he := congrArg (fun g => pairCoordinates h
    (σ g ((pairCoordinates h).symm (0,coefficient h a x)))) (diagonalWord_upper ha b)
  simp only [map_mul,Module.End.mul_apply,pairCoordinates_upper,
    pairCoordinates_diagonal h hd ha,LinearEquiv.apply_symm_apply,
    map_zero,zero_add] at he
  have hi := LinearMap.congr_fun (coefficient_inv_mul h hd ha) x
  change coefficient h a⁻¹ (coefficient h a x) = x at hi
  simpa only [hi,Module.End.mul_apply] using congrArg Prod.fst he


theorem coefficient_square (h : RootPair σ (weyl : SL(2,F)) A)
    (hd : ∀ a : F, a ≠ 0 → ∀ x ∈ A, σ (diagonalWord a) x ∈ A) (a : F) :
    coefficient h a * coefficient h a = coefficient h (a*a) := by
  simpa only [coefficient_one h weyl_mul_self upper_one_braid,mul_one] using
    coefficient_sandwich h hd a 1

theorem coefficient_commute (h : RootPair σ (weyl : SL(2,F)) A)
    (hd : ∀ a : F, a ≠ 0 → ∀ x ∈ A, σ (diagonalWord a) x ∈ A) (a b : F) :
    coefficient h a * coefficient h b = coefficient h b * coefficient h a := by
  have he := coefficient_square h hd (a+b)
  rw [CharTwo.add_mul_self,coefficient_add h _ _ (upper_add _ _),
    coefficient_add h _ _ (upper_add _ _),add_mul,mul_add,mul_add,
    coefficient_square h hd a,coefficient_square h hd b] at he
  have hz : coefficient h a * coefficient h b + coefficient h b * coefficient h a = 0 := by
    have hh : coefficient h (a*a) + coefficient h (b*b) +
        (coefficient h a * coefficient h b + coefficient h b * coefficient h a) =
        coefficient h (a*a) + coefficient h (b*b) + 0 := by
      rw [add_zero]
      convert he using 1
      abel
    exact add_left_cancel hh
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun hz x
  change coefficient h a (coefficient h b x) + coefficient h b (coefficient h a x) = 0 at hh
  have hn (y : A) : -y = y := by
    apply neg_eq_of_add_eq_zero_left
    simpa only [one_smul,show (1 : ZMod 2)+1=0 from rfl,zero_smul] using
      (add_smul (1 : ZMod 2) 1 y).symm
  exact (eq_neg_of_add_eq_zero_left hh).trans (hn _)

theorem coefficient_mul [Finite F] (h : RootPair σ (weyl : SL(2,F)) A)
    (hd : ∀ a : F, a ≠ 0 → ∀ x ∈ A, σ (diagonalWord a) x ∈ A) (a b : F) :
    coefficient h (a*b) = coefficient h a * coefficient h b := by
  have hs : Function.Surjective (fun x : F => x*x) := by
    apply Finite.surjective_of_injective
    intro x y hxy
    have he : x^2 = y^2 := by simpa only [pow_two] using hxy
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with he | he
    · exact he
    · simpa only [CharTwo.neg_eq] using he
  obtain ⟨c,rfl⟩ := hs a
  rw [← coefficient_sandwich h hd,← coefficient_square h hd]
  rw [mul_assoc,coefficient_commute h hd b c,← mul_assoc]

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

def coefficientHom [Finite F] (h : RootPair σ (weyl : SL(2,F)) A)
    (hd : ∀ a : F, a ≠ 0 → ∀ x ∈ A, σ (diagonalWord a) x ∈ A) :
    F →ₐ[ZMod 2] Module.End (ZMod 2) A where
  toFun := coefficient h
  map_zero' := coefficient_zero h
  map_one' := coefficient_one h weyl_mul_self upper_one_braid
  map_add' a b := coefficient_add h a b (upper_add a b)
  map_mul' a b := coefficient_mul h hd a b
  commutes' x := by
    fin_cases x
    · change coefficient h ((algebraMap (ZMod 2) F) 0) =
        (algebraMap (ZMod 2) (Module.End (ZMod 2) A)) 0
      rw [map_zero,map_zero,coefficient_zero]
    · change coefficient h ((algebraMap (ZMod 2) F) 1) =
        (algebraMap (ZMod 2) (Module.End (ZMod 2) A)) 1
      rw [map_one,map_one,coefficient_one h weyl_mul_self upper_one_braid]

theorem coefficient_coordinates [Finite F] [Finite M]
    (h : RootPair σ (weyl : SL(2,F)) A)
    (hd : ∀ a : F, a ≠ 0 → ∀ x ∈ A, σ (diagonalWord a) x ∈ A) :
    ∃ (m : ℕ) (e : A ≃ₗ[ZMod 2] (Fin m → F)),
      ∀ a x i, e (coefficient h a x) i = a * e x i := by
  let f := coefficientHom h hd
  let : Module F A := Module.compHom A f.toRingHom
  let e := (Module.finBasis F A).equivFun
  refine ⟨Module.finrank F A,e.restrictScalars (ZMod 2),?_⟩
  intro a x i
  exact congrFun (e.map_smul a x) i

noncomputable def pairPiCoordinates {m : ℕ} (e : A ≃ₗ[ZMod 2] (Fin m → F)) :
    (A × A) ≃ₗ[ZMod 2] (Fin m → Fin 2 → F) where
  toFun x i := ![e x.1 i,e x.2 i]
  invFun x := (e.symm (fun i => x i 0),e.symm (fun i => x i 1))
  left_inv x := by simp
  right_inv x := by
    funext i j
    fin_cases j <;> simp
  map_add' x y := by
    funext i j
    fin_cases j <;> simp
  map_smul' a x := by
    funext i j
    fin_cases j <;> simp

theorem pairPiCoordinates_apply {m : ℕ} (e : A ≃ₗ[ZMod 2] (Fin m → F))
    (x : A × A) (i : Fin m) : pairPiCoordinates e x i = ![e x.1 i,e x.2 i] := rfl

theorem natural_coordinates [Finite F] [Finite M]
    (h : RootPair σ (weyl : SL(2,F)) A)
    (hd : ∀ a : F, a ≠ 0 → ∀ x ∈ A, σ (diagonalWord a) x ∈ A) :
    NaturalCoordinates σ := by
  obtain ⟨m,e,he⟩ := coefficient_coordinates h hd
  let E := (pairCoordinates h).trans (pairPiCoordinates e)
  refine ⟨m,E,?_⟩
  intro g
  apply upper_weyl_induction
    (fun a => ∀ v i, E (σ a v) i = Matrix.mulVec a.val (E v i)) ?_ ?_ ?_ g
  · intro t v i
    change pairPiCoordinates e (pairCoordinates h (σ (upper t) v)) i =
      Matrix.mulVec (upper t).val (pairPiCoordinates e (pairCoordinates h v) i)
    rw [pairCoordinates_upper,pairPiCoordinates_apply,pairPiCoordinates_apply,upper_val]
    funext j
    fin_cases j <;> simp [he,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · intro v i
    change pairPiCoordinates e (pairCoordinates h (σ weyl v)) i =
      Matrix.mulVec weyl.val (pairPiCoordinates e (pairCoordinates h v) i)
    rw [pairCoordinates_weyl h weyl_mul_self,pairPiCoordinates_apply,pairPiCoordinates_apply]
    funext j
    fin_cases j <;> simp [weyl,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · intro a b ha hb v i
    rw [map_mul,Module.End.mul_apply,ha,hb,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mulVec_mulVec]

end Representation.SL2SylowFixedRecognition.RootCoordinates
